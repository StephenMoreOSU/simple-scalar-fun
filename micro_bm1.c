
#include <stdio.h>

#define LOOP_SZ 10000
int main(void)
{
    int i,x,y;
    x = 20;
    for(i=0;i<LOOP_SZ;i++)
    {
        y = x + i;
    }
    y = 10;
    x = 10;
    return 0;
}