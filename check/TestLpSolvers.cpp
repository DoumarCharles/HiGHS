#include <fstream>

#include "HCheckConfig.h"
#include "Highs.h"
#include "catch.hpp"

const bool dev_run = false;

void testDualObjective(const std::string model) {
  HighsStatus return_status;

  Highs highs;
  highs.setOptionValue("output_flag", dev_run);
  std::string model_file =
      std::string(HIGHS_DIR) + "/check/instances/" + model + ".mps";
  highs.readModel(model_file);
  return_status = highs.run();
  REQUIRE(return_status == HighsStatus::kOk);
  double dual_objective;
  return_status = highs.getDualObjectiveValue(dual_objective);
  REQUIRE(return_status == HighsStatus::kOk);
  double primal_objective = highs.getInfo().objective_function_value;
  double relative_primal_dual_gap =
      std::fabs(primal_objective - dual_objective) /
      std::max(1.0, std::fabs(primal_objective));
  REQUIRE(relative_primal_dual_gap < 1e-12);

  highs.resetThreadScheduler(true);
}

TEST_CASE("mip-with-lp-solver", "[highs_lp_solver]") {
  // When solving the relaxation of a MIP. Exposed #1406
  HighsStatus status;
  Highs highs;
  highs.setOptionValue("output_flag", dev_run);
  std::string filename =
      std::string(HIGHS_DIR) + "/check/instances/small_mip.mps";
  status = highs.readModel(filename);
  REQUIRE(status == HighsStatus::kOk);
  highs.setOptionValue("solver", kIpmString);
  status = highs.run();
  REQUIRE(status == HighsStatus::kOk);

  highs.resetThreadScheduler(true);
}

TEST_CASE("dual-objective-upper-bound", "[highs_lp_solver]") {
  std::string filename;
  HighsStatus status;
  HighsModelStatus model_status;
  bool bool_status;
  const double min_objective_function_value = -11.6389290663705;
  const double max_objective_function_value = 111.650960689315;
  const double smaller_min_objective_bound = -110.0;
  const double larger_min_objective_bound = -45.876;
  const double use_max_objective_bound = 150.0;
  double save_objective_bound;
  Highs highs;
  if (!dev_run) highs.setOptionValue("output_flag", false);
  const HighsInfo& info = highs.getInfo();

  //  status = highs.setOptionValue("log_dev_level",
  //  kHighsLogDevLevelVerbose);
  //  highs.setOptionValue("log_dev_level", 3);
  //  highs.setOptionValue("highs_analysis_level", 4);

  double error;
  filename = std::string(HIGHS_DIR) + "/check/instances/e226.mps";
  status = highs.readModel(filename);
  REQUIRE(status == HighsStatus::kOk);

  auto testHeader = [&](const std::string& text,
                        const double* objective_bound = nullptr) {
    std::string line =
        objective_bound
            ? highsFormatToString("%s %11.4g", text.c_str(), *objective_bound)
            : text;
    if (dev_run) highsPrintStringAsHeading(line);
  };

  // Solve vanilla
  testHeader("Solving vanilla LP");
  status = highs.run();
  REQUIRE(status == HighsStatus::kOk);

  model_status = highs.getModelStatus();
  REQUIRE(model_status == HighsModelStatus::kOptimal);

  error = fabs((info.objective_function_value - min_objective_function_value) /
               min_objective_function_value);
  if (dev_run) printf("\nOptimal objective value error = %g\n", error);
  REQUIRE(error < 1e-14);

  // Set dual objective value upper bound after saving the default value
  status = highs.getOptionValue("objective_bound", save_objective_bound);
  REQUIRE(status == HighsStatus::kOk);

  status = highs.setOptionValue("objective_bound", larger_min_objective_bound);
  REQUIRE(status == HighsStatus::kOk);

  // Solve again
  testHeader(
      "Solving LP with presolve, and larger dual objective value upper bound "
      "of ",
      &larger_min_objective_bound);
  status = highs.setBasis();
  REQUIRE(status == HighsStatus::kOk);

  status = highs.run();
  REQUIRE(status == HighsStatus::kOk);

  // Switch off presolve
  status = highs.setOptionValue("presolve", "off");
  REQUIRE(status == HighsStatus::kOk);

  // Solve again
  // This larger dual objective value upper bound is satisfied during phase 2
  testHeader(
      "Solving LP without presolve, and larger dual objective value upper "
      "bound of ",
      &larger_min_objective_bound);
  status = highs.clearSolver();
  REQUIRE(status == HighsStatus::kOk);

  status = highs.run();
  REQUIRE(status == HighsStatus::kOk);

  model_status = highs.getModelStatus();
  REQUIRE(model_status == HighsModelStatus::kObjectiveBound);

  // Solve again
  // This smaller dual objective value upper bound is satisfied at the start of
  // phase 2
  testHeader(
      "Solving LP without presolve, and smaller dual objective value upper "
      "bound of ",
      &smaller_min_objective_bound);
  status = highs.setOptionValue("objective_bound", smaller_min_objective_bound);
  REQUIRE(status == HighsStatus::kOk);

  status = highs.setBasis();
  REQUIRE(status == HighsStatus::kOk);

  status = highs.run();
  REQUIRE(status == HighsStatus::kOk);

  model_status = highs.getModelStatus();
  REQUIRE(model_status == HighsModelStatus::kObjectiveBound);

  // Solve as maximization and ensure that the dual objective value upper bound
  // is used
  bool_status =
      highs.changeObjectiveSense(ObjSense::kMaximize) == HighsStatus::kOk;
  REQUIRE(bool_status);

  status = highs.setOptionValue("objective_bound", use_max_objective_bound);
  REQUIRE(status == HighsStatus::kOk);

  // Solve again
  testHeader(
      "Solving LP as maximization without presolve, and dual objective value "
      "upper bound of ",
      &use_max_objective_bound);
  status = highs.setBasis();
  REQUIRE(status == HighsStatus::kOk);

  status = highs.run();
  REQUIRE(status == HighsStatus::kOk);

  model_status = highs.getModelStatus();
  REQUIRE(model_status == HighsModelStatus::kObjectiveBound);

  highs.resetThreadScheduler(true);
}

TEST_CASE("blending-lp-ipm", "[highs_lp_solver]") {
  Highs highs;
  highs.setOptionValue("output_flag", dev_run);
  HighsLp lp;
  lp.num_col_ = 2;
  lp.num_row_ = 2;
  lp.col_cost_ = {-8, -10};
  lp.col_lower_ = {0, 0};
  lp.col_upper_ = {kHighsInf, kHighsInf};
  lp.row_lower_ = {-kHighsInf, -kHighsInf};
  lp.row_upper_ = {80, 120};
  lp.a_matrix_.start_ = {0, 2, 4};
  lp.a_matrix_.index_ = {0, 1, 0, 1};
  lp.a_matrix_.value_ = {1, 1, 2, 4};
  highs.passModel(lp);
  highs.setOptionValue("solver", kIpmString);
  highs.setOptionValue("presolve", kHighsOffString);
  highs.run();
  HighsInfo info = highs.getInfo();
  if (dev_run) {
    printf("Num primal infeasibilities = %d\n",
           int(info.num_primal_infeasibilities));
    printf("Max primal infeasibility   = %g\n", info.max_primal_infeasibility);
    printf("Sum primal infeasibilities = %g\n",
           info.sum_primal_infeasibilities);
    printf("Num   dual infeasibilities = %d\n",
           int(info.num_dual_infeasibilities));
    printf("Max   dual infeasibility   = %g\n", info.max_dual_infeasibility);
    printf("Sum   dual infeasibilities = %g\n", info.sum_dual_infeasibilities);
  }
  REQUIRE(highs.getModelStatus() == HighsModelStatus::kOptimal);

  highs.resetThreadScheduler(true);
}

TEST_CASE("dual-objective-max", "[highs_lp_solver]") {
  Highs highs;
  highs.setOptionValue("output_flag", dev_run);
  HighsLp lp;
  lp.num_col_ = 2;
  lp.num_row_ = 2;
  lp.sense_ = ObjSense::kMaximize;
  lp.offset_ = 10;
  lp.col_cost_ = {8, 10};
  lp.col_lower_ = {0, 0};
  lp.col_upper_ = {kHighsInf, kHighsInf};
  lp.row_lower_ = {-kHighsInf, -kHighsInf};
  lp.row_upper_ = {80, 120};
  lp.a_matrix_.start_ = {0, 2, 4};
  lp.a_matrix_.index_ = {0, 1, 0, 1};
  lp.a_matrix_.value_ = {1, 1, 2, 4};
  highs.passModel(lp);
  highs.run();
  double dual_objective;
  HighsStatus return_status = highs.getDualObjectiveValue(dual_objective);
  REQUIRE(return_status == HighsStatus::kOk);
  double primal_objective = highs.getInfo().objective_function_value;
  double relative_primal_dual_gap =
      std::fabs(primal_objective - dual_objective) /
      std::max(1.0, std::fabs(primal_objective));
  REQUIRE(relative_primal_dual_gap < 1e-12);

  highs.resetThreadScheduler(true);
}

TEST_CASE("dual-objective", "[highs_lp_solver]") {
  testDualObjective("avgas");
  testDualObjective("adlittle");
  testDualObjective("etamacro");
  testDualObjective("stair");
}

void testStandardForm(const HighsLp& lp) {
  Highs highs;
  highs.setOptionValue("output_flag", dev_run);
  HighsInt sense = HighsInt(lp.sense_);
  REQUIRE(highs.passModel(lp) == HighsStatus::kOk);
  REQUIRE(highs.run() == HighsStatus::kOk);
  //  highs.writeSolution("", kSolutionStylePretty);
  double required_objective_function_value =
      highs.getInfo().objective_function_value;

  HighsInt num_col;
  HighsInt num_row;
  HighsInt num_nz;
  double offset;
  REQUIRE(highs.getStandardFormLp(num_col, num_row, num_nz, offset) ==
          HighsStatus::kOk);

  std::vector<double> cost(num_col);
  std::vector<double> rhs(num_row);
  std::vector<HighsInt> start(num_col + 1);
  std::vector<HighsInt> index(num_nz);
  std::vector<double> value(num_nz);
  REQUIRE(highs.getStandardFormLp(num_col, num_row, num_nz, offset, cost.data(),
                                  rhs.data(), start.data(), index.data(),
                                  value.data()) == HighsStatus::kOk);

  HighsLp standard_form_lp;
  standard_form_lp.num_col_ = num_col;
  standard_form_lp.num_row_ = num_row;
  standard_form_lp.offset_ = offset;
  standard_form_lp.col_cost_ = cost;
  standard_form_lp.col_lower_.assign(num_col, 0);
  standard_form_lp.col_upper_.assign(num_col, kHighsInf);
  standard_form_lp.row_lower_ = rhs;
  standard_form_lp.row_upper_ = rhs;
  standard_form_lp.a_matrix_.start_ = start;
  standard_form_lp.a_matrix_.index_ = index;
  standard_form_lp.a_matrix_.value_ = value;
  REQUIRE(highs.passModel(standard_form_lp) == HighsStatus::kOk);
  // highs.writeModel("");
  REQUIRE(highs.run() == HighsStatus::kOk);
  REQUIRE(highs.getModelStatus() == HighsModelStatus::kOptimal);
  highs.writeSolution("", kSolutionStylePretty);
  double objective_function_value =
      sense * highs.getInfo().objective_function_value;
  double objective_difference =
      std::fabs(objective_function_value - required_objective_function_value) /
      std::max(1.0, std::fabs(required_objective_function_value));
  REQUIRE(objective_difference < 1e-10);
  const bool look_at_presolved_lp = false;
  if (look_at_presolved_lp) {
    // Strange that presolve doesn't convert the constraints
    //
    // Ax-s = b; s >= 0 into Ax >= b
    REQUIRE(highs.passModel(standard_form_lp) == HighsStatus::kOk);
    REQUIRE(highs.presolve() == HighsStatus::kOk);
    HighsLp presolved_lp = highs.getPresolvedLp();
    REQUIRE(highs.passModel(presolved_lp) == HighsStatus::kOk);
    highs.writeModel("");
  }

  highs.resetThreadScheduler(true);
}

void testStandardFormModel(const std::string model) {
  const std::string model_file =
      std::string(HIGHS_DIR) + "/check/instances/" + model + ".mps";
  ;
  Highs highs;
  highs.setOptionValue("output_flag", dev_run);
  highs.readModel(model_file);
  HighsLp lp = highs.getLp();
  testStandardForm(lp);

  highs.resetThreadScheduler(true);
}

TEST_CASE("standard-form-mps", "[highs_lp_solver]") {
  testStandardFormModel("avgas");
  testStandardFormModel("afiro");
}

TEST_CASE("standard-form-lp", "[highs_lp_solver]") {
  HighsLp lp;
  lp.offset_ = -0.5;
  lp.num_col_ = 4;
  lp.num_row_ = 3;
  lp.col_cost_ = {1, 1, 1, -1};
  lp.col_lower_ = {1, -kHighsInf, -kHighsInf, -1};
  lp.col_upper_ = {kHighsInf, kHighsInf, 2, 3};
  lp.row_lower_ = {0, 1, -kHighsInf};
  lp.row_upper_ = {4, kHighsInf, 4};
  lp.a_matrix_.start_ = {0, 2, 4, 6, 8};
  lp.a_matrix_.index_ = {0, 2, 0, 1, 1, 2, 0, 2};
  lp.a_matrix_.value_ = {1, 1, 1, 1, 1, 1, 1, 1};

  testStandardForm(lp);
  Highs highs;
  highs.setOptionValue("output_flag", dev_run);

  std::vector<HighsInt> index;
  std::vector<double> value;
  // Add a fixed column and a fixed row, and maximize
  highs.passModel(lp);
  index = {0, 1, 2};
  value = {-1, 1, -1};
  REQUIRE(highs.addCol(-2.0, 1.0, 1.0, 3, index.data(), value.data()) ==
          HighsStatus::kOk);
  index = {0, 1, 2, 3};
  value = {-2, -1, 1, 3};
  REQUIRE(highs.addRow(1.0, 1.0, 4, index.data(), value.data()) ==
          HighsStatus::kOk);
  REQUIRE(highs.changeObjectiveSense(ObjSense::kMaximize) == HighsStatus::kOk);
  if (dev_run)
    printf(
        "\nNow test by adding a fixed column and a fixed row, and "
        "maximizing\n");
  testStandardForm(highs.getLp());

  highs.resetThreadScheduler(true);
}

TEST_CASE("standard-form-empty-lp", "[highs_lp_solver]") {
  // Exposed that standard_form_valid_ was not initialised if a model
  // had not been loaded - ie empty or built
  Highs h;
  h.setOptionValue("output_flag", dev_run);

  HighsInt num_col;
  HighsInt num_row;
  HighsInt num_nz;
  double offset;
  REQUIRE(h.getStandardFormLp(num_col, num_row, num_nz, offset) ==
          HighsStatus::kOk);
  REQUIRE(num_col == 0);
  REQUIRE(num_row == 0);
  REQUIRE(num_nz == 0);
}

TEST_CASE("simplex-stats", "[highs_lp_solver]") {
  Highs h;
  const HighsSimplexStats& simplex_stats = h.getSimplexStats();
  h.setOptionValue("output_flag", dev_run);
  std::string model_file =
      std::string(HIGHS_DIR) + "/check/instances/adlittle.mps";
  REQUIRE(h.readModel(model_file) == HighsStatus::kOk);

  REQUIRE(h.run() == HighsStatus::kOk);
  REQUIRE(simplex_stats.valid);
  REQUIRE(simplex_stats.iteration_count == 0);
  REQUIRE(simplex_stats.num_invert == 1);
  REQUIRE(simplex_stats.last_invert_num_el > 0);
  REQUIRE(simplex_stats.last_factored_basis_num_el > 0);
  REQUIRE(simplex_stats.col_aq_density == 0);
  REQUIRE(simplex_stats.row_ep_density == 0);
  REQUIRE(simplex_stats.row_ap_density == 0);
  REQUIRE(simplex_stats.row_DSE_density == 0);
  if (dev_run) h.reportSimplexStats(stdout);

  h.clearSolver();
  h.setOptionValue("presolve", kHighsOffString);
  REQUIRE(h.run() == HighsStatus::kOk);
  REQUIRE(simplex_stats.valid);
  REQUIRE(simplex_stats.iteration_count > 0);
  REQUIRE(simplex_stats.num_invert > 0);
  REQUIRE(simplex_stats.last_invert_num_el > 0);
  REQUIRE(simplex_stats.last_factored_basis_num_el > 0);
  REQUIRE(simplex_stats.col_aq_density > 0);
  REQUIRE(simplex_stats.row_ep_density > 0);
  REQUIRE(simplex_stats.row_ap_density > 0);
  REQUIRE(simplex_stats.row_DSE_density > 0);
  if (dev_run) h.reportSimplexStats(stdout);

  h.resetThreadScheduler(true);
}

TEST_CASE("use_warm_start", "[highs_lp_solver]") {
  Highs h;
  h.setOptionValue("output_flag", dev_run);
  std::string model_file =
      std::string(HIGHS_DIR) + "/check/instances/avgas.mps";
  REQUIRE(h.readModel(model_file) == HighsStatus::kOk);

  h.run();
  HighsInt required_iteration_count = h.getInfo().simplex_iteration_count;
  h.setOptionValue("use_warm_start", false);
  h.run();
  HighsInt iteration_count = h.getInfo().simplex_iteration_count;
  REQUIRE(iteration_count == required_iteration_count);

  h.resetThreadScheduler(true);
}

bool fileExists(const std::string& file_name) {
  std::ifstream infile(file_name);
  return static_cast<bool>(infile.good());
}

TEST_CASE("highs-files-lp", "[highs_lp_solver]") {
  const std::string test_name = Catch::getResultCapture().getCurrentTestName();
  const std::string write_solution_file = test_name + ".sol";
  const std::string write_basis_file = test_name + ".bas";
  const std::string write_model_file = test_name + ".mps";
  Highs h;
  h.setOptionValue("output_flag", dev_run);
  std::string model_file =
      std::string(HIGHS_DIR) + "/check/instances/avgas.mps";
  REQUIRE(h.readModel(model_file) == HighsStatus::kOk);

  h.setOptionValue("solution_file", write_solution_file);
  h.setOptionValue("write_basis_file", write_basis_file);
  h.setOptionValue("write_model_file", write_model_file);

  h.run();

  REQUIRE(fileExists(write_model_file));
  REQUIRE(fileExists(write_solution_file));
  REQUIRE(fileExists(write_basis_file));

  h.setOptionValue("solution_file", "");
  h.setOptionValue("write_basis_file", "");
  h.setOptionValue("write_model_file", "");

  h.setOptionValue("read_basis_file", write_basis_file);

  REQUIRE(h.readModel(write_model_file) == HighsStatus::kOk);

  h.run();

  REQUIRE(h.getInfo().simplex_iteration_count == 0);

  std::remove(write_model_file.c_str());
  std::remove(write_solution_file.c_str());
  std::remove(write_basis_file.c_str());

  h.resetThreadScheduler(true);
}

TEST_CASE("highs-files-mip", "[highs_lp_solver]") {
  const std::string test_name = Catch::getResultCapture().getCurrentTestName();
  const std::string write_solution_file = test_name + ".sol";
  const std::string write_basis_file = test_name + ".bas";
  const std::string write_model_file = test_name + ".mps";
  Highs h;
  h.setOptionValue("output_flag", dev_run);
  std::string model_file =
      std::string(HIGHS_DIR) + "/check/instances/flugpl.mps";
  REQUIRE(h.readModel(model_file) == HighsStatus::kOk);

  h.setOptionValue("solution_file", write_solution_file);
  h.setOptionValue("write_model_file", write_model_file);

  h.run();

  REQUIRE(fileExists(write_model_file));
  REQUIRE(fileExists(write_solution_file));

  h.setOptionValue("solution_file", "");
  h.setOptionValue("write_model_file", "");

  REQUIRE(h.readModel(write_model_file) == HighsStatus::kOk);
  h.setOptionValue("read_solution_file", write_solution_file);
  HighsStatus run_status = h.run();

  REQUIRE(run_status == HighsStatus::kOk);

  std::remove(write_model_file.c_str());
  std::remove(write_solution_file.c_str());

  h.resetThreadScheduler(true);
}

/*
TEST_CASE("highs-debug-level", "[highs_lp_solver]") {
  Highs h;
  h.setOptionValue("output_flag", dev_run);
  std::string model_file =
      std::string(HIGHS_DIR) + "/check/instances/avgas.mps";

  h.readModel(model_file);
  h.setOptionValue("solver", kIpmString);
  h.setOptionValue("highs_debug_level",  1);
  h.run();
  h.setOptionValue("highs_debug_level",  2);
  h.run();
  h.setOptionValue("highs_debug_level",  3);
  h.run();
  h.resetThreadScheduler(true);
}
*/
TEST_CASE("solver-string", "[highs_lp_solver]") {
  Highs h;
  h.setOptionValue("output_flag", dev_run);
  REQUIRE(h.setOptionValue(kSolverString, "fred") == HighsStatus::kError);
  REQUIRE(h.setOptionValue(kSolverString, kHighsChooseString) ==
          HighsStatus::kOk);
  REQUIRE(h.setOptionValue(kSolverString, kSimplexString) == HighsStatus::kOk);
  REQUIRE(h.setOptionValue(kSolverString, kIpmString) == HighsStatus::kOk);

#ifdef HIPO
  REQUIRE(h.setOptionValue(kSolverString, kHipoString) == HighsStatus::kOk);
#else
  REQUIRE(h.setOptionValue(kSolverString, kHipoString) == HighsStatus::kError);
#endif
  REQUIRE(h.setOptionValue(kSolverString, kIpxString) == HighsStatus::kOk);
  REQUIRE(h.setOptionValue(kSolverString, kPdlpString) == HighsStatus::kOk);
}

TEST_CASE("choose-lp-solver", "[highs_lp_solver]") {
  std::string model_file =
      std::string(HIGHS_DIR) + "/check/instances/avgas.mps";
  Highs h;
  h.setOptionValue("output_flag", dev_run);
  REQUIRE(h.readModel(model_file) == HighsStatus::kOk);

  REQUIRE(h.setOptionValue(kSolverString, kPdlpString) == HighsStatus::kOk);
  h.run();
  REQUIRE(h.getInfo().pdlp_iteration_count > 0);

  REQUIRE(h.setOptionValue(kSolverString, kIpmString) == HighsStatus::kOk);
  // h.setOptionValue("output_flag", true);
  h.run();
  REQUIRE(h.getInfo().ipm_iteration_count > 0);

  h.resetThreadScheduler(true);
}

TEST_CASE("releaseMemory", "[highs_lp_solver]") {
  std::string model_file =
      std::string(HIGHS_DIR) + "/check/instances/avgas.mps";
  Highs h;
  h.setOptionValue("output_flag", dev_run);

  // First solve
  REQUIRE(h.readModel(model_file) == HighsStatus::kOk);
  REQUIRE(h.run() == HighsStatus::kOk);
  REQUIRE(h.getModelStatus() == HighsModelStatus::kOptimal);
  double first_objective = h.getInfo().objective_function_value;

  // Release memory and verify we can solve again
  REQUIRE(h.releaseMemory() == HighsStatus::kOk);

  // Second solve on a different model
  std::string model_file2 =
      std::string(HIGHS_DIR) + "/check/instances/adlittle.mps";
  REQUIRE(h.readModel(model_file2) == HighsStatus::kOk);
  REQUIRE(h.run() == HighsStatus::kOk);
  REQUIRE(h.getModelStatus() == HighsModelStatus::kOptimal);
  double second_objective = h.getInfo().objective_function_value;

  // Verify objectives are different (different problems)
  REQUIRE(first_objective != second_objective);

  h.resetThreadScheduler(true);
}

TEST_CASE("issue-2300", "[highs_lp_solver]") {
  // After presolve, the only dual infeasibility at the start is that
  // of a free nonbasic variable. Dual phase 2 is forced, hands over to
  // dual phase 1 without iterating, and phase 1 must not then use the
  // list of free variables that phase 2 created
  std::string model_file =
      std::string(HIGHS_DIR) + "/check/instances/issue-2300.mps";
  Highs h;
  h.setOptionValue("output_flag", dev_run);
  if (dev_run) h.setOptionValue("log_dev_level", 1);
  REQUIRE(h.readModel(model_file) == HighsStatus::kOk);
  REQUIRE(h.run() == HighsStatus::kOk);
  REQUIRE(h.getModelStatus() == HighsModelStatus::kOptimal);
  const double optimal_objective = 4.0735475989e-04;
  REQUIRE(std::fabs(h.getInfo().objective_function_value - optimal_objective) <
          1e-12);

  h.resetThreadScheduler(true);
}

TEST_CASE("issue-3564", "[highs_lp_solver]") {
  const std::string test_name = Catch::getResultCapture().getCurrentTestName();
  std::string model_file = test_name + ".lp";
  FILE* file = fopen(model_file.c_str(), "w");
  fprintf(file, "%s",
          "min\n obj: +230.9345703125 x12 \nst\n r0: +0.34375 x1 +0.03125 x3 "
          ">= -849.4453125\n r4: +0.015625 x0 +224 x6 = +76.37109375\n r9: "
          "+2.75 x1 +84 x3 -0.0283203125 x6 +72 x12 = -1445.8564453125\n "
          "r17lo: -0.0390625 x0 +452 x3 >= -6094.146484375\n r17up: -0.0390625 "
          "x0 +452 x3 <= -6058.146484375\nbounds\n -2 <= x0\n -inf <= x1 <= "
          "9\n x3 free\n x6 free\n -inf <= x12 <= 39\nend\n");
  fclose(file);
  Highs h;
  h.setOptionValue("output_flag", dev_run);
  h.setOptionValue("log_dev_level", 1);
  REQUIRE(h.readModel(model_file) == HighsStatus::kOk);
  REQUIRE(h.run() == HighsStatus::kOk);
  REQUIRE(h.getModelStatus() == HighsModelStatus::kUnbounded);

  std::remove(model_file.c_str());

  h.resetThreadScheduler(true);
}

TEST_CASE("issue-3726", "[highs_lp_solver]") {
  const std::string test_name = Catch::getResultCapture().getCurrentTestName();
  std::string model_file = test_name + ".lp";
  FILE* file = fopen(model_file.c_str(), "w");
  fprintf(file, "%s",
          "Maximize\nobj: 5 x + 4 y + 3 z\nSubject To\nc1: 2 x + 3 y + z <= "
          "5\nc2: 4 x + y + 2 z <= 11\nc3: 3 x + 4 y + 2 z <= 8\nBounds\n0 <= "
          "x <= 10\n0 <= y <= 10\n0 <= z <= 10\n"
          "End\n");

  fclose(file);

  Highs h;
  std::string text;
  auto testObjectiveBound = [&](const double objective_bound,
                                const HighsModelStatus require_model_status) {
    h.clearSolver();
    std::string line =
        highsFormatToString("%s %11.4g", text.c_str(), objective_bound);
    if (dev_run) highsPrintStringAsHeading(line);
    h.setOptionValue("objective_bound", objective_bound);
    REQUIRE(h.run() == HighsStatus::kOk);
    REQUIRE(h.getModelStatus() == require_model_status);
  };

  h.setOptionValue("output_flag", dev_run);
  //  h.setOptionValue("log_dev_level", 3);
  //  h.setOptionValue("highs_analysis_level", 4);
  REQUIRE(h.readModel(model_file) == HighsStatus::kOk);
  REQUIRE(h.run() == HighsStatus::kOk);
  const double optimal_objective_value = h.getObjectiveValue();
  const double attainable_objective_bound = 20;
  const double unattainable_objective_bound = 10;
  REQUIRE(attainable_objective_bound > optimal_objective_value);
  REQUIRE(unattainable_objective_bound < optimal_objective_value);

  text = "Solving max LP with attainable objective bound of ";
  testObjectiveBound(attainable_objective_bound,
                     HighsModelStatus::kObjectiveBound);
  text = "Solving max LP with unattainable objective bound of ";
  testObjectiveBound(unattainable_objective_bound, HighsModelStatus::kOptimal);

  // Now solve the problem as a MIP, with objective_bound = -20
  //
  // objective_bound is designed for LPs, but (see #3726) solving a
  // MIP with optimal objective 13 when objective_bound = -20 results
  // in it being declared infeasible immediately since
  // HighsMipSolver.cpp:206 mipdata_->getDomain().infeasible() is
  // true!
  const double mip_objective_bound = -20;
  std::vector<HighsVarType> integrality = {
      HighsVarType::kInteger, HighsVarType::kInteger, HighsVarType::kInteger};
  REQUIRE(h.changeColsIntegrality(0, 2, integrality.data()) ==
          HighsStatus::kOk);
  REQUIRE(h.writeModel(model_file) == HighsStatus::kOk);

  HighsModelStatus require_model_status =
      HighsModelStatus::kInfeasible;  // HighsModelStatus::kOptimal;
  text = "Solving max MIP with objective bound of ";
  testObjectiveBound(mip_objective_bound, require_model_status);

  std::remove(model_file.c_str());

  h.resetThreadScheduler(true);
}

const std::vector<std::string> solvers{kPdlpString, kHiPdlpString, kIpxString
#ifdef HIPO
                                       ,
                                       kHipoString
#endif
};

TEST_CASE("issue-3715", "[highs_lp_solver]") {
  const std::string test_name = Catch::getResultCapture().getCurrentTestName();
  std::string model_file = test_name + ".mps";
  FILE* file = fopen(model_file.c_str(), "w");
  fprintf(file, "%s",
          "NAME small2\nROWS\n N obj\n E s0\n E s1\n E s2\n E d0\n E d1\n E "
          "d2\n E d3\nCOLUMNS\n    f0_0 obj 9\n    f0_0 s0 1\n    f0_0 d0 1\n  "
          "  f0_1 obj 4\n    f0_1 s0 1\n    f0_1 d1 1\n    f0_2 obj 7\n    "
          "f0_2 s0 1\n    f0_2 d2 1\n    f0_3 obj 1\n    f0_3 s0 1\n    f0_3 "
          "d3 1\n    f1_0 obj 8\n    f1_0 s1 1\n    f1_0 d0 1\n    f1_1 obj "
          "8\n    f1_1 s1 1\n    f1_1 d1 1\n    f1_2 obj 8\n    f1_2 s1 1\n    "
          "f1_2 d2 1\n    f1_3 obj 7\n    f1_3 s1 1\n    f1_3 d3 1\n    f2_0 "
          "obj 8\n    f2_0 s2 1\n    f2_0 d0 1\n    f2_1 obj 4\n    f2_1 s2 "
          "1\n    f2_1 d1 1\n    f2_2 obj 7\n    f2_2 s2 1\n    f2_2 d2 1\n    "
          "f2_3 obj 2\n    f2_3 s2 1\n    f2_3 d3 1\nRHS\n    rhs s0 7267\n    "
          "rhs s1 14623\n    rhs s2 6263\n    rhs d0 7615\n    rhs d1 5870\n   "
          " rhs d2 6327\n    rhs d3 8341\n    rhs obj 147155\nENDATA\n");
  fclose(file);

  Highs h;
  h.setOptionValue("output_flag", dev_run);
  h.setOptionValue("run_crossover", kHighsOffString);
  h.setOptionValue("presolve", kHighsOffString);
  REQUIRE(h.readModel(model_file) == HighsStatus::kOk);
  for (auto& solver : solvers) {
    h.setOptionValue("solver", solver);
    std::string line = highsFormatToString("Solving with %s", solver.c_str());
    if (dev_run) highsPrintStringAsHeading(line);
    h.clearSolver();
    REQUIRE(h.run() == HighsStatus::kOk);
    REQUIRE(h.getModelStatus() == HighsModelStatus::kOptimal);
  }
  std::remove(model_file.c_str());

  h.resetThreadScheduler(true);
}

TEST_CASE("primal-cycling-phase-change", "[highs_lp_solver]") {
  // Feasible (x = (2, 0.75, 0, 1)) and unbounded (x3 increases). The
  // primal simplex phase 2 returned to bases visited in phase 1, which
  // was taken as cycling, and the solve ended with model status unknown
  HighsLp lp;
  lp.num_col_ = 4;
  lp.num_row_ = 3;
  lp.col_cost_ = {3, -3, 0, -1};
  lp.col_lower_ = {1, 0, 0, 0.5};
  lp.col_upper_ = {3, 0.75001, 1, kHighsInf};
  lp.row_lower_ = {2, -2.075, -kHighsInf};
  lp.row_upper_ = {2.5, -2.074, -0.6};
  lp.a_matrix_.format_ = MatrixFormat::kColwise;
  lp.a_matrix_.start_ = {0, 3, 4, 5, 6};
  lp.a_matrix_.index_ = {0, 1, 2, 1, 0, 2};
  lp.a_matrix_.value_ = {1, -1, 0.2, -0.1, -0.3, -1};
  for (const std::string presolve : {kHighsOnString, kHighsOffString}) {
    Highs h;
    h.setOptionValue("output_flag", dev_run);
    h.setOptionValue("presolve", presolve);
    REQUIRE(h.passModel(lp) == HighsStatus::kOk);
    REQUIRE(h.run() == HighsStatus::kOk);
    REQUIRE(h.getModelStatus() == HighsModelStatus::kUnbounded);
    h.resetThreadScheduler(true);
  }
}

TEST_CASE("dual-cycling-phase-change", "[highs_lp_solver]") {
  // LP of upstream issue 3289: feasible and bounded (sum of x is 1). The
  // dual simplex phase 2 returned to bases visited in phase 1, which was
  // taken as cycling, and the solve ended with model status unknown
  const HighsInt n = 1280;
  const double pi = 3.14159265358979323846;
  const double a[12] = {-7, -9, -16, 8, -1, 8, 9, 3, -2, 4, -5, -6};
  std::vector<double> t(n), c(n), w(n);
  std::vector<std::vector<double>> row(5, std::vector<double>(n));
  for (HighsInt j = 0; j < n; j++) {
    t[j] = 2 * pi * j / n;
    row[0][j] = 1;
    row[1][j] = std::cos(t[j]);
    row[2][j] = std::sin(t[j]);
    row[3][j] = std::cos(2 * t[j]);
    row[4][j] = std::sin(2 * t[j]);
    double v = 0;
    for (HighsInt k = 1; k <= 6; k++)
      v += a[2 * k - 2] / 16 * std::cos(k * t[j]) +
           a[2 * k - 1] / 16 * std::sin(k * t[j]);
    c[j] = v;
  }
  double c_min = c[0], c_max = c[0], w_sum = 0;
  for (HighsInt j = 0; j < n; j++) {
    c_min = std::min(c_min, c[j]);
    c_max = std::max(c_max, c[j]);
    w[j] = std::exp(3 * std::cos(t[j] - 2 * pi * 0.40154194513298813));
    w_sum += w[j];
  }
  HighsLp lp;
  lp.num_col_ = n;
  lp.num_row_ = 5;
  lp.col_lower_.assign(n, 0);
  lp.col_upper_.assign(n, kHighsInf);
  lp.row_lower_.assign(5, 0);
  lp.a_matrix_.format_ = MatrixFormat::kColwise;
  lp.a_matrix_.start_.clear();
  for (HighsInt j = 0; j < n; j++) {
    lp.col_cost_.push_back(-(c[j] - c_min) / (c_max - c_min));
    w[j] /= w_sum;
    lp.a_matrix_.start_.push_back(lp.a_matrix_.index_.size());
    for (HighsInt i = 0; i < 5; i++) {
      // Leave out the round-off values of cos and sin at multiples of
      // pi/2, which passModel would remove with a warning
      if (std::fabs(row[i][j]) <= 1e-9) continue;
      lp.a_matrix_.index_.push_back(i);
      lp.a_matrix_.value_.push_back(row[i][j]);
    }
  }
  lp.a_matrix_.start_.push_back(lp.a_matrix_.index_.size());
  for (HighsInt i = 0; i < 5; i++)
    for (HighsInt j = 0; j < n; j++) lp.row_lower_[i] += row[i][j] * w[j];
  lp.row_upper_ = lp.row_lower_;
  Highs h;
  h.setOptionValue("output_flag", dev_run);
  h.setOptionValue("solver", kSimplexString);
  h.setOptionValue("simplex_strategy", kSimplexStrategyDual);
  h.setOptionValue("simplex_scale_strategy", 1);
  h.setOptionValue("parallel", kHighsOffString);
  h.setOptionValue("presolve", kHighsOffString);
  h.setOptionValue("primal_feasibility_tolerance", 1e-10);
  h.setOptionValue("dual_feasibility_tolerance", 1e-10);
  h.setOptionValue("simplex_iteration_limit", 1000);
  REQUIRE(h.passModel(lp) == HighsStatus::kOk);
  REQUIRE(h.run() == HighsStatus::kOk);
  REQUIRE(h.getModelStatus() == HighsModelStatus::kOptimal);
  REQUIRE(std::fabs(h.getInfo().objective_function_value + 0.53164328324541) <
          1e-9);
  h.resetThreadScheduler(true);
}

TEST_CASE("primal-cycling-phase1-cost-change", "[highs_lp_solver]") {
  // Infeasible: x3 = 2 and row 1 give x1 = 3.5 > 3. The primal simplex
  // phase 1 returned to a basis visited before basic variables became
  // feasible, so with other phase 1 costs, which was taken as cycling, and
  // the solve ended with model status unknown
  HighsLp lp;
  lp.num_col_ = 5;
  lp.num_row_ = 4;
  lp.sense_ = ObjSense::kMaximize;
  lp.col_cost_ = {3, 0, 0, 0, 0};
  lp.col_lower_ = {-4, -2, 1, 2, -kHighsInf};
  lp.col_upper_ = {kHighsInf, 3, 5, 2, 4};
  lp.row_lower_ = {8, 3, 8.5, -kHighsInf};
  lp.row_upper_ = {10, 3, kHighsInf, 1.5};
  lp.a_matrix_.format_ = MatrixFormat::kColwise;
  lp.a_matrix_.start_ = {0, 0, 3, 5, 6, 7};
  lp.a_matrix_.index_ = {1, 2, 3, 0, 2, 1, 0};
  lp.a_matrix_.value_ = {2, -1, -3, 1, 0.5, -2, 1};
  for (const std::string presolve : {kHighsOnString, kHighsOffString}) {
    Highs h;
    h.setOptionValue("output_flag", dev_run);
    h.setOptionValue("presolve", presolve);
    REQUIRE(h.passModel(lp) == HighsStatus::kOk);
    REQUIRE(h.run() == HighsStatus::kOk);
    REQUIRE(h.getModelStatus() == HighsModelStatus::kInfeasible);
    h.resetThreadScheduler(true);
  }
}

// Margin by which a dual ray is a Farkas proof of infeasibility for the LP:
// the distance between the range of ray^T A x over the column bounds and
// the range of ray^T r over the row bounds, positive if they are disjoint
static double farkasMargin(const HighsLp& lp, const std::vector<double>& ray) {
  double max_ray = 0;
  for (HighsInt iRow = 0; iRow < lp.num_row_; iRow++)
    max_ray = std::max(max_ray, std::fabs(ray[iRow]));
  const double zero = 1e-9 * max_ray;
  double row_min = 0, row_max = 0, col_min = 0, col_max = 0;
  for (HighsInt iRow = 0; iRow < lp.num_row_; iRow++) {
    const double y = ray[iRow];
    if (std::fabs(y) <= zero) continue;
    const double at_lower = y * lp.row_lower_[iRow];
    const double at_upper = y * lp.row_upper_[iRow];
    row_min += std::min(at_lower, at_upper);
    row_max += std::max(at_lower, at_upper);
  }
  for (HighsInt iCol = 0; iCol < lp.num_col_; iCol++) {
    double z = 0;
    for (HighsInt iEl = lp.a_matrix_.start_[iCol];
         iEl < lp.a_matrix_.start_[iCol + 1]; iEl++)
      z += ray[lp.a_matrix_.index_[iEl]] * lp.a_matrix_.value_[iEl];
    if (std::fabs(z) <= zero) continue;
    const double at_lower = z * lp.col_lower_[iCol];
    const double at_upper = z * lp.col_upper_[iCol];
    col_min += std::min(at_lower, at_upper);
    col_max += std::max(at_lower, at_upper);
  }
  return std::max(row_min - col_max, col_min - row_max);
}

// Counts the log lines saying that primal simplex is used since dual
// simplex ended with model status unknown, and those saying that the
// primal simplex phase 1 dual values are a proof of infeasibility. The
// logging callback is only called when output_flag is true
static void countPrimalAfterUnknown(Highs& h, HighsInt& count,
                                    HighsInt& proof_count) {
  h.setOptionValue("output_flag", true);
  h.setOptionValue("log_to_console", dev_run);
  h.setCallback([&count, &proof_count](
                    int callback_type, const std::string& message,
                    const HighsCallbackOutput*, HighsCallbackInput*, void*) {
    if (callback_type != kCallbackLogging) return;
    if (message.find("model status unknown: using primal simplex") !=
        std::string::npos)
      count++;
    if (message.find("phase 1 dual values are a proof") != std::string::npos)
      proof_count++;
  });
  h.startCallback(kCallbackLogging);
}

TEST_CASE("issue-3418", "[highs_lp_solver]") {
  // Infeasible, since row 10 is x10 = -1e6 with x10 >= 0. In dual phase 2
  // a row with no entering column and no proof of infeasibility is made
  // taboo. A row chosen later proves infeasibility, but the taboo basis
  // change gave model status unknown
  HighsLp lp;
  lp.num_col_ = 12;
  lp.num_row_ = 11;
  lp.col_cost_ = {0, 0, 0, 0, -1, 1e-6, 1e-6, 1e-6, 5e-7, 5e-7, 5e-7, 0};
  lp.col_lower_.assign(12, 0);
  lp.col_upper_.assign(12, kHighsInf);
  lp.row_lower_ = {0, 0, 0, 0, 0, 0, 0, -1.7e6, -1e6, -1e6, -1e6};
  lp.row_upper_ = {kHighsInf, 0, 0, 0, 0, 0, 0, -1.7e6, -1e6, -1e6, -1e6};
  lp.a_matrix_.format_ = MatrixFormat::kColwise;
  lp.a_matrix_.start_ = {0, 2, 4, 6, 8, 9, 11, 13, 15, 17, 19, 21, 23};
  lp.a_matrix_.index_ = {2, 3, 3, 4, 4, 5, 5, 6, 6,  1, 2, 3,
                         1, 7, 5, 8, 5, 9, 5, 6, 10, 7, 0};
  lp.a_matrix_.value_ = {0.95542, -1.11036, 0.9,  -0.8,     0.7, -1, 0.8, -1,
                         0.8,     -1.04666, -1,   -1.11036, -1,  2,  -2,  1,
                         -1,      1,        -0.8, -1,       1,   -1, -0.9};
  Highs h;
  HighsInt primal_after_unknown = 0;
  HighsInt phase1_proof = 0;
  countPrimalAfterUnknown(h, primal_after_unknown, phase1_proof);
  h.setOptionValue("presolve", kHighsOffString);
  REQUIRE(h.passModel(lp) == HighsStatus::kOk);
  REQUIRE(h.run() == HighsStatus::kOk);
  REQUIRE(h.getModelStatus() == HighsModelStatus::kInfeasible);
  // Dual simplex proves infeasibility without primal simplex
  REQUIRE(primal_after_unknown == 0);
  bool has_dual_ray = false;
  std::vector<double> dual_ray(lp.num_row_);
  REQUIRE(h.getDualRay(has_dual_ray, dual_ray.data()) == HighsStatus::kOk);
  REQUIRE(has_dual_ray);
  const double farkas_margin = farkasMargin(lp, dual_ray);
  INFO("Farkas margin " << farkas_margin);
  REQUIRE(farkas_margin > 0);
  h.resetThreadScheduler(true);
}

TEST_CASE("issue-3418-primal", "[highs_lp_solver]") {
  // Infeasible, since row r1344 is -0.03 c1544 = 3e5 with c1544 >= 0. In
  // dual simplex the proof of infeasibility from every primal infeasible
  // row fails on a fresh factorization, so primal simplex is used. Its
  // phase 1 dual values must prove infeasibility
  const std::string filename =
      std::string(HIGHS_DIR) + "/check/instances/issue-3418.mps";
  Highs h;
  HighsInt primal_after_unknown = 0;
  HighsInt phase1_proof = 0;
  countPrimalAfterUnknown(h, primal_after_unknown, phase1_proof);
  h.setOptionValue("presolve", kHighsOffString);
  REQUIRE(h.readModel(filename) == HighsStatus::kOk);
  REQUIRE(h.run() == HighsStatus::kOk);
  REQUIRE(h.getModelStatus() == HighsModelStatus::kInfeasible);
  REQUIRE(primal_after_unknown == 1);
  REQUIRE(phase1_proof == 1);
  h.resetThreadScheduler(true);
}

TEST_CASE("issue-3418-phase1", "[highs_lp_solver]") {
  // Infeasible. Dual simplex hands over to primal simplex. Its phase 1
  // dual values prove infeasibility when they are scaled and their
  // small values are not set to zero
  const std::string filename =
      std::string(HIGHS_DIR) + "/check/instances/issue-3418-phase1.mps";
  Highs h;
  HighsInt primal_after_unknown = 0;
  HighsInt phase1_proof = 0;
  countPrimalAfterUnknown(h, primal_after_unknown, phase1_proof);
  h.setOptionValue("presolve", kHighsOffString);
  REQUIRE(h.readModel(filename) == HighsStatus::kOk);
  REQUIRE(h.run() == HighsStatus::kOk);
  REQUIRE(h.getModelStatus() == HighsModelStatus::kInfeasible);
  REQUIRE(primal_after_unknown == 1);
  REQUIRE(phase1_proof == 1);
  h.resetThreadScheduler(true);
}

TEST_CASE("issue-3418-phase1-small", "[highs_lp_solver]") {
  // Infeasible. As issue-3418-phase1, but the phase 1 dual values
  // include small values that are needed for the proof
  const std::string filename =
      std::string(HIGHS_DIR) + "/check/instances/issue-3418-phase1-small.mps";
  Highs h;
  HighsInt primal_after_unknown = 0;
  HighsInt phase1_proof = 0;
  countPrimalAfterUnknown(h, primal_after_unknown, phase1_proof);
  h.setOptionValue("presolve", kHighsOffString);
  REQUIRE(h.readModel(filename) == HighsStatus::kOk);
  REQUIRE(h.run() == HighsStatus::kOk);
  REQUIRE(h.getModelStatus() == HighsModelStatus::kInfeasible);
  REQUIRE(primal_after_unknown == 1);
  REQUIRE(phase1_proof == 1);
  h.resetThreadScheduler(true);
}
