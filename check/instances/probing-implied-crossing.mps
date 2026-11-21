NAME fuzz
* x* 1 0.25 -0.75 -0.75 1.0000019073486328 2
ROWS
 N obj
 L r0
 L r1
 L r2
 E r3
COLUMNS
    MARKER    'MARKER'    'INTORG'
    x0    obj    0
    x0    r1    -0.3
    MARKER    'MARKER'    'INTEND'
    x1    obj    -1
    x1    r1    -1
    x1    r2    0.2
    x2    obj    1
    x2    r0    0.1
    x2    r1    4
    x2    r2    -1
    x3    obj    0
    x3    r0    1
    x3    r2    -5
    x3    r3    -1
    x4    obj    0
    x4    r2    1e+01
    MARKER    'MARKER'    'INTORG'
    x5    obj    0
    x5    r2    -1e+01
    MARKER    'MARKER'    'INTEND'
RHS
    RHS    r0    -0.825
    RHS    r1    -3.549999999999999
    RHS    r2    -5.449980926513671
    RHS    r3    0.75
RANGES
    RNG    r0    1.1102230246251565e-16
    RNG    r1    1.3322676295501878e-15
BOUNDS
 FR BND x0
 LO BND x1 0.25
 UP BND x1 1.25
 LO BND x2 -0.75
 UP BND x2 -0.749995231628418
 FR BND x3
 LO BND x4 1.0000019073486328
 UP BND x4 1.0000019073486328
 LO BND x5 1.999995231628418
 UP BND x5 2
ENDATA
