#ifndef VRA_CONFIG_H
#define VRA_CONFIG_H

#ifndef M
#define M 1
#endif

// if enabled set annotation ranges
#ifndef OLDVRA
#define OLDVRA 0
#endif

#ifndef RMIN
#define RMIN -0.5
#endif

#ifndef RMAX
#define RMAX 1
#endif

#ifndef RMIN_POS
#define RMIN_POS 1
#endif

#ifndef RMAX_POS
#define RMAX_POS 2.5
#endif

// row size (array and matrix)
#ifndef R
#define R 500
#endif

// column size (matrix)
#ifndef C
#define C 300
#endif

// row size for geometric (array and matrix)
#ifndef R_SMALL
#define R_SMALL 10
#endif

// column size for geometric (matrix)
#ifndef C_SMALL
#define C_SMALL 5
#endif

#ifndef N
#define N 500
#endif

// iteration for geometric
#ifndef N_SMALL
#define N_SMALL 10
#endif

#define PB_STR(x) #x
#define PB_XSTR(x) PB_STR(x)

#endif // VRA_CONFIG_H
