#include "stdio.h"
#include "glpk.h"

int main() {
    printf("GLPK Version: %s\n", glp_version());
    return 0;
}
