/**CFile****************************************************************

  FileName    [cecPat.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Combinational equivalence checking.]

  Synopsis    [Simulation pattern manager.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: cecPat.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cecInt.h"
// #define assert(expr)    (expr)?NULL:exit(0);

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Cec_ManPatStoreNum( Cec_ManPat_t * p, int Num )
{
    unsigned x = (unsigned)Num;
    assert( Num >= 0 );
    while ( x & ~0x7f )
    {
        Vec_StrPush( p->vStorage, (char)((x & 0x7f) | 0x80) );
        x >>= 7;
    }
    Vec_StrPush( p->vStorage, (char)x );
}

/**Function*************************************************************

  Synopsis    []

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Cec_ManPatRestoreNum( Cec_ManPat_t * p )
{
    int ch, i, x = 0;
    for ( i = 0; (ch = Vec_StrEntry(p->vStorage, p->iStart++)) & 0x80; i++ )
        x |= (ch & 0x7f) << (7 * i);
    return x | (ch << (7 * i));
}

/**Function*************************************************************

  Synopsis    []

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Cec_ManPatStore( Cec_ManPat_t * p, Vec_Int_t * vPat )
{
    int i, Number, NumberPrev;
    assert( Vec_IntSize(vPat) > 0 );
    Cec_ManPatStoreNum( p, Vec_IntSize(vPat) );
    NumberPrev = Vec_IntEntry( vPat, 0 );
    Cec_ManPatStoreNum( p, NumberPrev );
    Vec_IntForEachEntryStart( vPat, Number, i, 1 )
    // for ( i = 1; (i < Vec_IntSize(vPat)) && (((Number) = Vec_IntEntry(vPat, i)), 1); i++ )
    {
        assert( NumberPrev < Number );
        Cec_ManPatStoreNum( p, Number - NumberPrev );
        NumberPrev = Number;
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Cec_ManPatRestore( Cec_ManPat_t * p, Vec_Int_t * vPat )
{
    int i, Size, Number;
    Vec_IntClear( vPat );
    Size = Cec_ManPatRestoreNum( p );
    Number = Cec_ManPatRestoreNum( p );
    Vec_IntPush( vPat, Number );
    for ( i = 1; i < Size; i++ )
    {
        Number += Cec_ManPatRestoreNum( p );
        Vec_IntPush( vPat, Number );
    }
    assert( Vec_IntSize(vPat) == Size );
}

// return 1 for true, 0 for false
int Cec_ManPatPrintTFICNF_rec( Cec_ManSat_t * pSat, Gia_Man_t * p, Gia_Obj_t * pObj , lbool print_tfi){
    if ( Gia_ObjIsTravIdCurrent(p, pObj) ){
        return pObj->fMark1;
    }
    Gia_ObjSetTravIdCurrent(p, pObj);
    if ( Gia_ObjIsCi(pObj) ){
        return pObj->fMark1 = Cec_ObjSatVarValue( pSat, pObj );
    }

    int value0 = Cec_ManPatPrintTFICNF_rec( pSat, p, Gia_ObjFanin0(pObj), print_tfi);
    int value1 = Cec_ManPatPrintTFICNF_rec( pSat, p, Gia_ObjFanin1(pObj), print_tfi );
    int objId0 = Gia_ObjId(p, Gia_ObjFanin0(pObj));
    int objId1 = Gia_ObjId(p, Gia_ObjFanin1(pObj));
    int thisObjId = Gia_ObjId(p, pObj);

    int ret = (value0^Gia_ObjFaninC0(pObj)) & (value1^Gia_ObjFaninC1(pObj)) ;
    pObj->fMark1 = ret;

    if(print_tfi){
        printf("%5d(%s) <- %c%5d(%s) & %c%5d(%s)\n", ret?thisObjId:-thisObjId, Gia_ObjType(pObj),
            Gia_ObjFaninC0(pObj)?'!':' ', value0?objId0:-objId0, Gia_ObjType(Gia_ObjFanin0(pObj)),
            Gia_ObjFaninC1(pObj)?'!':' ', value1?objId1:-objId1, Gia_ObjType(Gia_ObjFanin1(pObj)));
    }
    // if(ret != pObj->fMark1){
    //     printf("pSat: %p, pAig: %p\n", pSat, p);
    //     printf("node %d, ret: %d fMark1: %d \n", thisObjId, ret, pObj->fMark1);
    //     printf("%d %d & %d %d\n", Gia_ObjFaninC0(pObj), value0, Gia_ObjFaninC1(pObj), value1);
    //     printf("%d %d & %d %d\n", Gia_ObjFaninC0(pObj), Gia_ObjFanin0(pObj)->fMark1, Gia_ObjFaninC1(pObj), Gia_ObjFanin1(pObj)->fMark1);
    //     assert(false);
    // }
    return ret;
}


int Cec_ManPatPrintTFICNF( Cec_ManSat_t * pSat, Gia_Man_t * p, Gia_Obj_t * pObj ){
    Gia_ManIncrementTravId( p );
    lbool print_tfi = true;
    printf(">>>> print the TFI of node %d (cnf)\n", Gia_ObjId(p, pObj));
    int ret = Cec_ManPatPrintTFICNF_rec(pSat, p, pObj, print_tfi);
    
    printf("<<<< done with ret %d of node %d\n", ret, Gia_ObjId(p, pObj));
    return ret;
} 


/**Function*************************************************************

  Synopsis    [Derives satisfying assignment.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManPatComputePattern_rec( Cec_ManSat_t * pSat, Gia_Man_t * p, Gia_Obj_t * pObj, lbool print_tfi)
{
    int Counter = 0;
    if ( Gia_ObjIsTravIdCurrent(p, pObj) )
        return 0;
    Gia_ObjSetTravIdCurrent(p, pObj);
    if ( Gia_ObjIsCi(pObj) )
    {
        pObj->fMark1 = Cec_ObjSatVarValue( pSat, pObj );
        // printf("fMark %d for obj %d\n", pObj->fMark1, Gia_ObjId(p, pObj));
        return 1;
    }
    assert( Gia_ObjIsAnd(pObj) );
    Counter += Cec_ManPatComputePattern_rec( pSat, p, Gia_ObjFanin0(pObj) , print_tfi);
    Counter += Cec_ManPatComputePattern_rec( pSat, p, Gia_ObjFanin1(pObj) , print_tfi);
    // fMarks is the value of the variable pObj, not SAT or UNSAT
    // pObj->fMark1 = 1 iff both of its fanins are true
    pObj->fMark1 = (Gia_ObjFanin0(pObj)->fMark1 ^ Gia_ObjFaninC0(pObj)) & 
                   (Gia_ObjFanin1(pObj)->fMark1 ^ Gia_ObjFaninC1(pObj));
    if(print_tfi){
        int objId0 = Gia_ObjId(p, Gia_ObjFanin0(pObj));
        int objId1 = Gia_ObjId(p, Gia_ObjFanin1(pObj));
        int thisObjId = Gia_ObjId(p, pObj);
        printf("%5d(%s) <- %c%5d(%s) & %c%5d(%s)\n", pObj->fMark1?thisObjId:-thisObjId, Gia_ObjType(pObj),
            Gia_ObjFaninC0(pObj)?'!':' ', Gia_ObjFanin0(pObj)->fMark1?objId0:-objId0, Gia_ObjType(Gia_ObjFanin0(pObj)),
            Gia_ObjFaninC1(pObj)?'!':' ', Gia_ObjFanin1(pObj)->fMark1?objId1:-objId1, Gia_ObjType(Gia_ObjFanin1(pObj)));
    }
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Derives satisfying assignment.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManPatComputePattern1_rec( Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Int_t * vPat )
{
    if ( Gia_ObjIsTravIdCurrent(p, pObj) )
        return;
    Gia_ObjSetTravIdCurrent(p, pObj);
    if ( Gia_ObjIsCi(pObj) )
    {
        Vec_IntPush( vPat, Abc_Var2Lit( Gia_ObjCioId(pObj), pObj->fMark1==0 ) );
        return;
    }
    assert( Gia_ObjIsAnd(pObj) );
    // true at obj
    if ( pObj->fMark1 == 1 )
    {
        Cec_ManPatComputePattern1_rec( p, Gia_ObjFanin0(pObj), vPat );
        Cec_ManPatComputePattern1_rec( p, Gia_ObjFanin1(pObj), vPat );
    }
    else
    // false at obj, at lease one of the childs is false
    {
        if(!((Gia_ObjFanin0(pObj)->fMark1 ^ Gia_ObjFaninC0(pObj)) == 0 || (Gia_ObjFanin1(pObj)->fMark1 ^ Gia_ObjFaninC1(pObj)) == 0))
            printf("assert failed at pObj %d\n", Gia_ObjId(p, pObj));
        assert( (Gia_ObjFanin0(pObj)->fMark1 ^ Gia_ObjFaninC0(pObj)) == 0 || (Gia_ObjFanin1(pObj)->fMark1 ^ Gia_ObjFaninC1(pObj)) == 0 );
        if ( (Gia_ObjFanin0(pObj)->fMark1 ^ Gia_ObjFaninC0(pObj)) == 0 )
            Cec_ManPatComputePattern1_rec( p, Gia_ObjFanin0(pObj), vPat );
        else
            Cec_ManPatComputePattern1_rec( p, Gia_ObjFanin1(pObj), vPat );
    }
}

/**Function*************************************************************

  Synopsis    [Derives satisfying assignment.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManPatComputePattern2_rec( Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Int_t * vPat )
{
    if ( Gia_ObjIsTravIdCurrent(p, pObj) )
        return;
    Gia_ObjSetTravIdCurrent(p, pObj);
    if ( Gia_ObjIsCi(pObj) )
    {
        Vec_IntPush( vPat, Abc_Var2Lit( Gia_ObjCioId(pObj), pObj->fMark1==0 ) );
        return;
    }
    assert( Gia_ObjIsAnd(pObj) );
    if ( pObj->fMark1 == 1 )
    {
        Cec_ManPatComputePattern2_rec( p, Gia_ObjFanin0(pObj), vPat );
        Cec_ManPatComputePattern2_rec( p, Gia_ObjFanin1(pObj), vPat );
    }
    else
    {
        assert( (Gia_ObjFanin0(pObj)->fMark1 ^ Gia_ObjFaninC0(pObj)) == 0 || (Gia_ObjFanin1(pObj)->fMark1 ^ Gia_ObjFaninC1(pObj)) == 0 );
        if ( (Gia_ObjFanin1(pObj)->fMark1 ^ Gia_ObjFaninC1(pObj)) == 0 )
            Cec_ManPatComputePattern2_rec( p, Gia_ObjFanin1(pObj), vPat );
        else
            Cec_ManPatComputePattern2_rec( p, Gia_ObjFanin0(pObj), vPat );
    }
}

/**Function*************************************************************

  Synopsis    [Derives satisfying assignment.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManPatComputePattern3_rec( Gia_Man_t * p, Gia_Obj_t * pObj )
{
    int Value0, Value1, Value;
    if ( Gia_ObjIsTravIdCurrent(p, pObj) )
        return (pObj->fMark1 << 1) | pObj->fMark0;
    Gia_ObjSetTravIdCurrent(p, pObj);
    if ( Gia_ObjIsCi(pObj) )
    {
        pObj->fMark0 = 1;
        pObj->fMark1 = 1;
        return GIA_UND;
    }
    assert( Gia_ObjIsAnd(pObj) );
    Value0 = Cec_ManPatComputePattern3_rec( p, Gia_ObjFanin0(pObj) );
    Value1 = Cec_ManPatComputePattern3_rec( p, Gia_ObjFanin1(pObj) );
    Value = Gia_XsimAndCond( Value0, Gia_ObjFaninC0(pObj), Value1, Gia_ObjFaninC1(pObj) );
    pObj->fMark0 =  (Value & 1);
    pObj->fMark1 = ((Value >> 1) & 1);
    return Value;
}

/**Function*************************************************************

  Synopsis    [Derives satisfying assignment.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManPatVerifyPattern( Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Int_t * vPat )
{
    Gia_Obj_t * pTemp;
    int i, Value;
    Gia_ManIncrementTravId( p );
    Vec_IntForEachEntry( vPat, Value, i )
    {
        pTemp = Gia_ManCi( p, Abc_Lit2Var(Value) );
//        assert( Abc_LitIsCompl(Value) != (int)pTemp->fMark1 );
        if ( pTemp->fMark1 )
        {
            pTemp->fMark0 = 0;
            pTemp->fMark1 = 1;
        }
        else
        {
            pTemp->fMark0 = 1;
            pTemp->fMark1 = 0;
        }
        Gia_ObjSetTravIdCurrent( p, pTemp );
    }
    Value = Cec_ManPatComputePattern3_rec( p, Gia_ObjFanin0(pObj) );
    Value = Gia_XsimNotCond( Value, Gia_ObjFaninC0(pObj) );
    if ( Value != GIA_ONE )
        Abc_Print( 1, "Cec_ManPatVerifyPattern(): Verification failed.\n" );
    assert( Value == GIA_ONE );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManPatComputePattern4_rec( Gia_Man_t * p, Gia_Obj_t * pObj )
{
    if ( Gia_ObjIsTravIdCurrent(p, pObj) )
        return;
    Gia_ObjSetTravIdCurrent(p, pObj);
    pObj->fMark0 = 0;
    if ( Gia_ObjIsCi(pObj) )
        return;
    assert( Gia_ObjIsAnd(pObj) );
    Cec_ManPatComputePattern4_rec( p, Gia_ObjFanin0(pObj) );
    Cec_ManPatComputePattern4_rec( p, Gia_ObjFanin1(pObj) );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManPatCleanMark0( Gia_Man_t * p, Gia_Obj_t * pObj )
{
    assert( Gia_ObjIsCo(pObj) );
    Gia_ManIncrementTravId( p );
    Cec_ManPatComputePattern4_rec( p, Gia_ObjFanin0(pObj) );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManPatSavePattern( Cec_ManPat_t * pMan, Cec_ManSat_t *  p, Gia_Obj_t * pObj )
{
    // printf("saving pattern\n");
    lbool testing = false; 
    lbool print_tfi = false;
    Vec_Int_t * vPat;
    int nPatLits;
    abctime clkTotal = Abc_Clock();
//    abctime clk;
    assert( Gia_ObjIsCo(pObj) );
    pMan->nPats++;
    pMan->nPatsAll++;
    // compute values in the cone of influence
//clk = Abc_Clock();
    // printf("begin nTravIds %d\n", p->pAig->nTravIds);
    Gia_ManIncrementTravId( p->pAig );

    if(testing) printf("    beforeComputePattern %d: %d %d %d\n", Gia_ObjId(p->pAig, pObj), Gia_ObjFaninC0(pObj), Gia_ObjFanin0(pObj)->fMark1, (Gia_ObjFanin0(pObj)->fMark1 ^ Gia_ObjFaninC0(pObj)));
    if(print_tfi)   printf(">>>> print the TFI of node %d (cnf)\n", Gia_ObjId(p->pAig, pObj));
    nPatLits = Cec_ManPatComputePattern_rec( p, p->pAig, Gia_ObjFanin0(pObj) , print_tfi);
    
// Cec_ManPatPrintTFICNF( p, p->pAig, pObj);

    // printf("end nTravIds %d\n", p->pAig->nTravIds);
    if(print_tfi){
        int objId0 = Gia_ObjId(p->pAig, Gia_ObjFanin0(pObj));
        int objId1 = Gia_ObjId(p->pAig, Gia_ObjFanin1(pObj));
        printf("co: %5d(%s) <- %c%5d(%s) & %c%5d(%s)\n", Gia_ObjId(p->pAig, pObj), Gia_ObjType(pObj),
            Gia_ObjFaninC0(pObj)?'!':' ', Gia_ObjFanin0(pObj)->fMark1?objId0:-objId0, Gia_ObjType(Gia_ObjFanin0(pObj)),
            Gia_ObjFaninC1(pObj)?'!':' ', Gia_ObjFanin1(pObj)->fMark1?objId1:-objId1, Gia_ObjType(Gia_ObjFanin1(pObj)));
        printf("<<<< done\n");
    }
    if(testing) printf("    afterComputePattern:  %d %d %d\n", Gia_ObjFaninC0(pObj), Gia_ObjFanin0(pObj)->fMark1, (Gia_ObjFanin0(pObj)->fMark1 ^ Gia_ObjFaninC0(pObj)));
    // Gia_ObjChild0(pObj) should be SAT
    assert( (Gia_ObjFanin0(pObj)->fMark1 ^ Gia_ObjFaninC0(pObj)) == 1 );
    pMan->nPatLits += nPatLits;
    pMan->nPatLitsAll += nPatLits;
//pMan->timeFind += Abc_Clock() - clk;
    // compute sensitizing path
//clk = Abc_Clock();
    Vec_IntClear( pMan->vPattern1 );
    Gia_ManIncrementTravId( p->pAig );
    Cec_ManPatComputePattern1_rec( p->pAig, Gia_ObjFanin0(pObj), pMan->vPattern1 );
    // compute sensitizing path
    Vec_IntClear( pMan->vPattern2 );
    Gia_ManIncrementTravId( p->pAig );
    Cec_ManPatComputePattern2_rec( p->pAig, Gia_ObjFanin0(pObj), pMan->vPattern2 );
    // compare patterns
    vPat = Vec_IntSize(pMan->vPattern1) < Vec_IntSize(pMan->vPattern2) ? pMan->vPattern1 : pMan->vPattern2;
    pMan->nPatLitsMin += Vec_IntSize(vPat);
    pMan->nPatLitsMinAll += Vec_IntSize(vPat);
//pMan->timeShrink += Abc_Clock() - clk;
    // verify pattern using ternary simulation
//clk = Abc_Clock();
//    Cec_ManPatVerifyPattern( p->pAig, pObj, vPat );
//pMan->timeVerify += Abc_Clock() - clk;
    // sort pattern
//clk = Abc_Clock();
    Vec_IntSort( vPat, 0 );
//pMan->timeSort += Abc_Clock() - clk;
    // save pattern
    Cec_ManPatStore( pMan, vPat );
    pMan->timeTotal += Abc_Clock() - clkTotal;
}

// Gia_ObjChild0(pObj) is SAT
void Cec_ManPatSavePattern_Pthread( Cec_ManPat_t *  pMan, Cec_ManSat_t *  p, Gia_Obj_t * pObj , int iThread)
{
    lbool testing = false;
    lbool print_tfi = false;
    if(testing) printf("    entering %d of Cec_ManPatSavePattern_Pthread\n", iThread);
    Vec_Int_t * vPat;
    int nPatLits;
    abctime clkTotal = Abc_Clock();
    assert( Gia_ObjIsCo(pObj) );
    pMan->nPats++;
    pMan->nPatsAll++;
    // compute values in the cone of influence
// printf("begin nTravIds %d at %p (thread %d)\n", p->pAig->nTravIds, &p->pAig->pTravIds, iThread);
    Gia_ManIncrementTravId( p->pAig );

    if(testing) printf("    pSat: %p, pAig: %p, thread: %d\n", p, p->pAig, iThread);    
    if(testing) printf("    before %d: %d %d %d\n", Gia_ObjId(p->pAig, pObj), Gia_ObjFaninC0(pObj), Gia_ObjFanin0(pObj)->fMark1, (Gia_ObjFanin0(pObj)->fMark1 ^ Gia_ObjFaninC0(pObj)));

    if(print_tfi)   printf(">>>> print the TFI of node %d (cnf) nTravIds %d thread %d \n", Gia_ObjId(p->pAig, pObj), p->pAig->nTravIds, iThread);

    nPatLits = Cec_ManPatComputePattern_rec( p, p->pAig, Gia_ObjFanin0(pObj) , print_tfi);

    if(print_tfi){
        int objId0 = Gia_ObjId(p->pAig, Gia_ObjFanin0(pObj));
        int objId1 = Gia_ObjId(p->pAig, Gia_ObjFanin1(pObj));
        printf("co: %5d(%s) <- %c%5d(%s) & %c%5d(%s)\n", Gia_ObjId(p->pAig, pObj), Gia_ObjType(pObj),
            Gia_ObjFaninC0(pObj)?'!':' ', Gia_ObjFanin0(pObj)->fMark1?objId0:-objId0, Gia_ObjType(Gia_ObjFanin0(pObj)),
            Gia_ObjFaninC1(pObj)?'!':' ', Gia_ObjFanin1(pObj)->fMark1?objId1:-objId1, Gia_ObjType(Gia_ObjFanin1(pObj)));
        printf("<<<< done\n");
    }

// Cec_ManPatPrintTFICNF( p, p->pAig, Gia_ObjFanin0(pObj) );

    if(testing) printf("    after: %d %d %d\n", Gia_ObjFaninC0(pObj), Gia_ObjFanin0(pObj)->fMark1, (Gia_ObjFanin0(pObj)->fMark1 ^ Gia_ObjFaninC0(pObj)));
    // if(! ((Gia_ObjFanin0(pObj)->fMark1 ^ Gia_ObjFaninC0(pObj)) == 1 )){
    //     Gia_ManIncrementTravId( p->pAig );
    //     printf("detecting error at node %d thread %d!!!\n", Gia_ObjId(p->pAig, Gia_ObjFanin0(pObj)), iThread);
    //     // Cec_ManPatPrintTFICNF( p, p->pAig, pObj);
    //     Cec_ManPatPrintTFICNF( p, p->pAig, Gia_ObjFanin0(pObj) );
    //     printf("    after: %d %d %d thread %d\n", Gia_ObjFaninC0(pObj), Gia_ObjFanin0(pObj)->fMark1, (Gia_ObjFanin0(pObj)->fMark1 ^ Gia_ObjFaninC0(pObj)), iThread);
    //     // exit(0);
    //     // getchar();
    //     // Cec_ManTFIPrint(p->pAig, pObj);
    // }
    
    assert( (Gia_ObjFanin0(pObj)->fMark1 ^ Gia_ObjFaninC0(pObj)) == 1 );
    pMan->nPatLits += nPatLits;
    pMan->nPatLitsAll += nPatLits;
    // compute sensitizing path
    Vec_IntClear( pMan->vPattern1 );
    Gia_ManIncrementTravId( p->pAig );
    Cec_ManPatComputePattern1_rec( p->pAig, Gia_ObjFanin0(pObj), pMan->vPattern1 );
    // compute sensitizing path
    Vec_IntClear( pMan->vPattern2 );
    Gia_ManIncrementTravId( p->pAig );
    Cec_ManPatComputePattern2_rec( p->pAig, Gia_ObjFanin0(pObj), pMan->vPattern2 );
    // compare patterns
    vPat = Vec_IntSize(pMan->vPattern1) < Vec_IntSize(pMan->vPattern2) ? pMan->vPattern1 : pMan->vPattern2;
    pMan->nPatLitsMin += Vec_IntSize(vPat);
    pMan->nPatLitsMinAll += Vec_IntSize(vPat);
    // sort pattern
    Vec_IntSort( vPat, 0 );
    // save pattern
    Cec_ManPatStore( pMan, vPat );
    pMan->timeTotal += Abc_Clock() - clkTotal;
    if(testing) printf("    leaving %d of Cec_ManPatSavePattern_Pthread\n\n", iThread);
}


void Cec_ManPatSavePatternCSat( Cec_ManPat_t * pMan, Vec_Int_t * vPat )
{
    // sort pattern
    Vec_IntSort( vPat, 0 );
    // save pattern
    Cec_ManPatStore( pMan, vPat );
}

/**Function*************************************************************

  Synopsis    [Packs patterns into array of simulation info.]

  Description []
               
  SideEffects []

  SeeAlso     []

*************************************`**********************************/
int Cec_ManPatCollectTry( Vec_Ptr_t * vInfo, Vec_Ptr_t * vPres, int iBit, int * pLits, int nLits )
{
    unsigned * pInfo, * pPres;
    int i;
    for ( i = 0; i < nLits; i++ )
    {
        pInfo = (unsigned *)Vec_PtrEntry(vInfo, Abc_Lit2Var(pLits[i]));
        pPres = (unsigned *)Vec_PtrEntry(vPres, Abc_Lit2Var(pLits[i]));
        if ( Abc_InfoHasBit( pPres, iBit ) && 
             Abc_InfoHasBit( pInfo, iBit ) == Abc_LitIsCompl(pLits[i]) )
             return 0;
    }
    for ( i = 0; i < nLits; i++ )
    {
        pInfo = (unsigned *)Vec_PtrEntry(vInfo, Abc_Lit2Var(pLits[i]));
        pPres = (unsigned *)Vec_PtrEntry(vPres, Abc_Lit2Var(pLits[i]));
        Abc_InfoSetBit( pPres, iBit );
        if ( Abc_InfoHasBit( pInfo, iBit ) == Abc_LitIsCompl(pLits[i]) )
            Abc_InfoXorBit( pInfo, iBit );
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Packs patterns into array of simulation info.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Cec_ManPatCollectPatterns( Cec_ManPat_t *  pMan, int nInputs, int nWordsInit )
{
    Vec_Int_t * vPat = pMan->vPattern1;
    Vec_Ptr_t * vInfo, * vPres;
    int k, kMax = -1, nPatterns = 0;
    int iStartOld = pMan->iStart;
    int nWords = nWordsInit;
    int nBits = 32 * nWords;
    abctime clk = Abc_Clock();
    vInfo = Vec_PtrAllocSimInfo( nInputs, nWords );
    Gia_ManRandomInfo( vInfo, 0, 0, nWords );
    vPres = Vec_PtrAllocSimInfo( nInputs, nWords );
    Vec_PtrCleanSimInfo( vPres, 0, nWords );
    while ( pMan->iStart < Vec_StrSize(pMan->vStorage) )
    {
        nPatterns++;
        Cec_ManPatRestore( pMan, vPat );
        for ( k = 1; k < nBits; k++, k += ((k % (32 * nWordsInit)) == 0) )
            if ( Cec_ManPatCollectTry( vInfo, vPres, k, (int *)Vec_IntArray(vPat), Vec_IntSize(vPat) ) )
                break;
        kMax = Abc_MaxInt( kMax, k );
        if ( k == nBits-1 )
        {
            Vec_PtrReallocSimInfo( vInfo );
            Gia_ManRandomInfo( vInfo, 0, nWords, 2*nWords );
            Vec_PtrReallocSimInfo( vPres );
            Vec_PtrCleanSimInfo( vPres, nWords, 2*nWords );
            nWords *= 2;
            nBits *= 2;
        }
    }
    Vec_PtrFree( vPres );
    pMan->nSeries = Vec_PtrReadWordsSimInfo(vInfo) / nWordsInit;
    pMan->timePack += Abc_Clock() - clk;
    pMan->timeTotal += Abc_Clock() - clk;
    pMan->iStart = iStartOld;
    if ( pMan->fVerbose )
    {
        Abc_Print( 1, "Total = %5d. Max used = %5d. Full = %5d. Series = %d. ", 
            nPatterns, kMax, nWordsInit*32, pMan->nSeries );
        ABC_PRT( "Time", Abc_Clock() - clk );
        Cec_ManPatPrintStats( pMan );
    }
    return vInfo;
}


/**Function*************************************************************

  Synopsis    [Packs patterns into array of simulation info.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Cec_ManPatPackPatterns( Vec_Int_t * vCexStore, int nInputs, int nRegs, int nWordsInit )
{
    Vec_Int_t * vPat;
    Vec_Ptr_t * vInfo, * vPres;
    int k, nSize, iStart, kMax = 0, nPatterns = 0;
    int nWords = nWordsInit;
    int nBits = 32 * nWords;
//    int RetValue;
    assert( nRegs <= nInputs );
    vPat  = Vec_IntAlloc( 100 );

    vInfo = Vec_PtrAllocSimInfo( nInputs, nWords );
    Vec_PtrCleanSimInfo( vInfo, 0, nWords );
    Gia_ManRandomInfo( vInfo, nRegs, 0, nWords );

    vPres = Vec_PtrAllocSimInfo( nInputs, nWords );
    Vec_PtrCleanSimInfo( vPres, 0, nWords );
    iStart = 0;
    while ( iStart < Vec_IntSize(vCexStore) )
    {
        nPatterns++;
        // skip the output number
        iStart++;
        // get the number of items
        nSize = Vec_IntEntry( vCexStore, iStart++ );
        if ( nSize <= 0 )
            continue;
        // extract pattern
        Vec_IntClear( vPat );
        for ( k = 0; k < nSize; k++ )
            Vec_IntPush( vPat, Vec_IntEntry( vCexStore, iStart++ ) );
        // add pattern to storage
        for ( k = 1; k < nBits; k++, k += ((k % (32 * nWordsInit)) == 0) )
            if ( Cec_ManPatCollectTry( vInfo, vPres, k, (int *)Vec_IntArray(vPat), Vec_IntSize(vPat) ) )
                break;

//        k = kMax + 1;
//        RetValue = Cec_ManPatCollectTry( vInfo, vPres, k, (int *)Vec_IntArray(vPat), Vec_IntSize(vPat) );
//        assert( RetValue == 1 );

        kMax = Abc_MaxInt( kMax, k );
        if ( k == nBits-1 )
        {
            Vec_PtrReallocSimInfo( vInfo );
            Vec_PtrCleanSimInfo( vInfo, nWords, 2*nWords );
            Gia_ManRandomInfo( vInfo, nRegs, nWords, 2*nWords );

            Vec_PtrReallocSimInfo( vPres );
            Vec_PtrCleanSimInfo( vPres, nWords, 2*nWords );
            nWords *= 2;
            nBits *= 2;
        }
    }
//    Abc_Print( 1, "packed %d patterns into %d vectors (out of %d)\n", nPatterns, kMax, nBits );
    Vec_PtrFree( vPres );
    Vec_IntFree( vPat );
    return vInfo;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

