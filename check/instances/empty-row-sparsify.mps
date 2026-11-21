NAME fuzz
* x* 1 0 0 -1
ROWS
 N obj
 E r0
 E r1
 E r2
 E r3
 E r4
COLUMNS
    MARKER    'MARKER'    'INTORG'
    x0    obj    0.001
    x0    r0    0.7
    x0    r1    1.5
    x0    r2    -1.5
    x0    r3    15
    x0    r4    3
    x1    obj    0.001
    x1    r0    -2
    x1    r1    -5
    x1    r2    5
    x1    r3    -5e+01
    x1    r4    -1e+01
    MARKER    'MARKER'    'INTEND'
    x2    obj    1
    x2    r1    -0.2
    x2    r2    0.2
    x2    r3    -2
    x2    r4    -0.4
    MARKER    'MARKER'    'INTORG'
    x3    obj    0.5
    x3    r0    0.7
    x3    r1    1.5
    x3    r2    -1.5
    x3    r3    15
    x3    r4    3
    MARKER    'MARKER'    'INTEND'
RHS
RANGES
BOUNDS
 LO BND x0 0
 PL BND x0
 LO BND x1 0
 UP BND x1 1
 LO BND x2 0
 UP BND x2 0
 LO BND x3 -1
 UP BND x3 -1
ENDATA
