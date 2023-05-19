# ABC: System for Sequential Logic Synthesis and Formal Verification

ABC is always changing but the current snapshot is believed to be stable. 

## Version Description: 

annotation: There is no much modification. This version can help me understand the flow better.
try to split the sat solver into two sub sat solver
To switch between them, see src/proof/cec/cecCore.c/Cec_ManSatSweeping (around L480)
Main modifications happen at cecSolve.c/Cec_ManSatSolve_Dual

Online note can be found at: [ABC note](https://docs.google.com/document/d/1M-UTdjznJdqUcuBmLw1-TUuy5CijGcvozut0IyyAIt8/edit)

## Compiling and run:

` make ABC_USE_NO_READLINE=1 -j20 `
` ./abc -c "&r i10.aig; &ps; &fraig -v; &ps" `
` ./abc -c "&r logic_my_suite/voter.aig; &ps; &fraig -v; &ps" `
` ./abc -c "&r logic_my_suite/ctrl.aig; &ps; &fraig -v; &ps" `

multitheads:

` ./abc -c "&r i10.aig; &ps; &fraig -v -T 10; &ps" `
` ./abc -c "&r logic_my_suite/voter.aig; &ps; &fraig -v -T 10; &ps" `
` ./abc -c "&r logic_my_suite/ctrl.aig; &ps; &fraig -v -T 10; &ps" `

tips: try sin.aig and voter.aig, which work faster with multithreads
or i2c.aig router.aig

how to add -g in makefile optionally ??

## to visualize:
use command `&show`, and then convert the .ps into .pdf

logic_my_suite/ctrl.aig : a small instance

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


## In order to generate my own .aig, 
` ./abc -c "read reconv.eqn; strash; &get; &w test.aig" `
