
int* search( int* arr, int length, int target )
{
    int cur_val;
    /* Loop invariant:
       There exists i such that old(length) == length + i,
       the sub-array [old(arr), .., old(arr)+i) doesn't contain the
       target value, and arr == old(arr) + i. */
    while( length > 0 )
    {
        cur_val = *arr;
        if( cur_val == target )
            return( arr );

        arr++;
        length--;
    }

    return( 0 );
}

int search_alt( int* arr, int length, int target )
{
    int i = 0;

    while( i < length )
    {
        int cur_val = arr[i];
        if( cur_val == target )
            return( i );

        i++;
    }

    return( -1 );
}
