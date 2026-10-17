set pagination off
set print pretty off
set confirm off
set breakpoint pending on
set print elements 0
set width 0
break HighsTableauSeparator.cpp:232
commands
  silent
  printf "== tableau base row (first generateCut, line 232)\n"
  print fracvar.basisIndex
  print fracvar.fractionality
  print fracvar.row_ep
  print baseRowInds
  print -elements 200 -- baseRowVals
  continue
end
break HighsTableauSeparator.cpp:237
commands
  silent
  printf "== tableau base row (second generateCut, line 237)\n"
  print baseRowInds
  print baseRowVals
  continue
end
run
printf "== stopped\n"
bt 14
frame function HighsDebugSol::checkCut
print (double)violation.hi + (double)violation.lo
print mipsolver->mipdata_->feastol
print rhs
print Rlen
print Rindex[0]@Rlen
print Rvalue[0]@Rlen
print debugSolution
frame function HighsCutGeneration::generateCut
print rhs_
print rowlen
print inds_
print vals_
