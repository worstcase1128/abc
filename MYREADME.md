# ABC: System for Sequential Logic Synthesis and Formal Verification

ABC is always changing but the current snapshot is believed to be stable. 

## Version Description: 

annotation: There is no much modification. This version can help me understand the flow better.

Online note can be found at: [ABC note](https://docs.google.com/document/d/1M-UTdjznJdqUcuBmLw1-TUuy5CijGcvozut0IyyAIt8/edit)

## Compiling:

`make ABC_USE_NO_READLINE=1 -j20`


Running the demo program by running the binary in the command-line mode:

    [...] ~/abc> ./abc
    UC Berkeley, ABC 1.01 (compiled Oct  6 2012 19:05:18)
    abc 01> r i10.aig; b; ps; b; rw -l; rw -lz; b; rw -lz; b; ps; cec
    i10          : i/o =  257/  224  lat =    0  and =   2396  lev = 37
    i10          : i/o =  257/  224  lat =    0  and =   1851  lev = 35
    Networks are equivalent.

    Or can try:
    &r i10.aig ; &fraig ; &ps
    div.aig  
    r: read
    b: balance
    ps: print_stats
    rw: rewrite

