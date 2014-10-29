#include "necla.h"

int __llbmc_main(int f){
    int comf_level = 0;
    switch (f){
    case -10:
        comf_level = -100;
        break;
    case 0:
        comf_level = -90;
        break;
    case 10:
        comf_level = -50;
        break;
    case 20:
        comf_level = -10;
        break;
    case 30:
        comf_level = -10;
        break;
    case 40:
        comf_level = -5;
        break;
    case 50:
        comf_level = 0;
        break;
    case 60:
        comf_level = 10;
        break;
    case 70:
        comf_level = 20;
        break;
    case 80:
        comf_level = 30;
        break;
    case 90:
        comf_level = 0;
        break;
    case 100:
        comf_level = -10;
        break;
    case 110:
        comf_level = -100;
        break;
    default:
        comf_level = 100;
    }

    if (comf_level >= 0 && comf_level <= 20){
        ASSERT(f >= 50 );
        ASSERT(f <= 80);
    }

    return 1;
}
