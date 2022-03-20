#include <stdio.h>
#define ITERS 10000
#define ARR_SZ 100
int main(void)
{
    //this program will have many read after writes
    int i;
    int arr[ITERS];
    arr[0] = 1;
    for(i=1;i<ITERS;i++)
    {
        arr[i] = arr[i-1];
    }
}