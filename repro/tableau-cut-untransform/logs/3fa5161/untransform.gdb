set pagination off
set confirm off
set breakpoint pending on
set print elements 0
set width 0
break HighsCutGeneration.cpp:1160
commands
  silent
  printf "== before untransform: rowlen=%d rhs=%.17g\n", rowlen, rhs.hi + rhs.lo
  print inds_
  print vals_
  continue
end
break HighsTransformedLp.cpp:598
commands
  silent
  printf "== untransform, before cleanup: tmpRhs=%.17g (+%.17g)\n", tmpRhs.hi, tmpRhs.lo
  set $k = 0
  while $k < vectorsum.nonzeroinds.size()
    set $c = vectorsum.nonzeroinds[$k]
    printf "   col %d  val=%.17g (+%.3g)  lb=%.17g ub=%.17g\n", $c, vectorsum.values[$c].hi, vectorsum.values[$c].lo, globaldom_.col_lower_[$c], globaldom_.col_upper_[$c]
    set $k = $k + 1
  end
  continue
end
break HighsTransformedLp.cpp:603
commands
  silent
  printf "== untransform, after cleanup: abort=%d tmpRhs=%.17g\n", abort, tmpRhs.hi + tmpRhs.lo
  continue
end
run
printf "== stopped at assertion\n"
