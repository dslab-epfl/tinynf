#pragma once

// Note that the Click build process greps this file for the constants

#define RTE_VER_YEAR 17
#define RTE_VER_MONTH 11
#define RTE_VER_MINOR 0
#define RTE_VER_RELEASE 16

#define RTE_VERSION_NUM(a,b,c,d) ((a) << 24 | (b) << 16 | (c) << 8 | (d))
#define RTE_VERSION RTE_VERSION_NUM(RTE_VER_YEAR, RTE_VER_MONTH, RTE_VER_MINOR, RTE_VER_RELEASE)
