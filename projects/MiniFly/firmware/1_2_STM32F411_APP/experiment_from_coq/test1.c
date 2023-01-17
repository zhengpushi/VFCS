
#include <stdbool.h>

bool fun1 () {
    bool x;
    x = (true & !(x));
    
}

void test() {
    bool b1,b2;
    
    b1 = fun1();
}
