/**CFile****************************************************************

  FileName    [cecSweep.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Combinational equivalence checking.]

  Synopsis    [SAT sweeping manager.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: cecSweep.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cecInt.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs limited speculative reduction.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Cec_ManFraSpecReduction( Cec_ManFra_t * p )
{
    lbool testing = true;
    lbool dtesting = false; // detailed 
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj, * pRepr = NULL;
    int iRes0, iRes1, iRepr, iNode, iMiter;
    int i, fCompl, * piCopies, * pDepths;
    Gia_ManSetPhase( p->pAig );
    Vec_IntClear( p->vXorNodes );
    if ( p->pPars->nLevelMax )
        Gia_ManLevelNum( p->pAig );
    pNew = Gia_ManStart( Gia_ManObjNum(p->pAig) );
    pNew->pName = Abc_UtilStrsav( p->pAig->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pAig->pName );
    Gia_ManHashAlloc( pNew );
    piCopies = ABC_FALLOC( int, Gia_ManObjNum(p->pAig) );
    pDepths  = ABC_CALLOC( int, Gia_ManObjNum(p->pAig) );
    piCopies[0] = 0;
    if(testing) printf(">>>Cec_ManFraSpecReduction\n");
    // Gia_ManPrintStats( pNew, NULL );
    if(testing) printf("    p->pAig size: %d\n", p->pAig->nObjs);
    int count1 = 0, count2=0, count3=0, count4=0;
    Gia_ManForEachObj1( p->pAig, pObj, i )
    {
        if ( Gia_ObjIsCi(pObj) ) 
        {
            piCopies[i] = Gia_ManAppendCi( pNew );
// printf("1 p[%d]=%d\n", i, piCopies[i]);
            continue;
        }
        if ( Gia_ObjIsCo(pObj) ) 
            continue;
        if ( piCopies[Gia_ObjFaninId0(pObj,i)] == -1 ||
             piCopies[Gia_ObjFaninId1(pObj,i)] == -1 )
             continue;
        iRes0 = Abc_LitNotCond( piCopies[Gia_ObjFaninId0(pObj,i)], Gia_ObjFaninC0(pObj) );
        iRes1 = Abc_LitNotCond( piCopies[Gia_ObjFaninId1(pObj,i)], Gia_ObjFaninC1(pObj) );
// printf("origin and %d&%d\n", toLitCond( Gia_ObjFaninId0(pObj,i), Gia_ObjFaninC0(pObj) ),  toLitCond( Gia_ObjFaninId1(pObj,i), Gia_ObjFaninC1(pObj)) );
        // return the lit of And gate in pNew
        iNode = piCopies[i] = Gia_ManHashAnd( pNew, iRes0, iRes1 );
if(dtesting) printf("2 p[%d]=%d %d&%d (ori %d&%d) total: %d\n", i, piCopies[i], iRes0, iRes1 , toLitCond( Gia_ObjFaninId0(pObj,i), Gia_ObjFaninC0(pObj) ),  toLitCond( Gia_ObjFaninId1(pObj,i), Gia_ObjFaninC1(pObj)), Gia_ManAndNum(pNew));
        count2++;
        pDepths[i] = Abc_MaxInt( pDepths[Gia_ObjFaninId0(pObj,i)], pDepths[Gia_ObjFaninId1(pObj,i)] );
        if ( Gia_ObjRepr(p->pAig, i) == GIA_VOID || Gia_ObjFailed(p->pAig, i) )
            continue;
        assert( Gia_ObjRepr(p->pAig, i) < i );
        int ori_repr = Gia_ObjRepr(p->pAig, i);
        iRepr = piCopies[ori_repr];
        if ( iRepr == -1 )
            continue;
        // 445
if(dtesting) printf("trying iRepr %d = piCopies[%d], iNode %d\n", iRepr, ori_repr, iNode);
        // the repr of i is ori_repr
if(dtesting) printf("node %d and %d in same equiv class\n", i, ori_repr);
        count3++;
        if ( Abc_LitRegular(iNode) == Abc_LitRegular(iRepr) )
            continue;
        // 395
        count4++;
        if ( p->pPars->nLevelMax && 
            (Gia_ObjLevelId(p->pAig, i)  > p->pPars->nLevelMax || 
             Gia_ObjLevelId(p->pAig, Abc_Lit2Var(iRepr)) > p->pPars->nLevelMax) )
            continue;
        if ( p->pPars->fDualOut )
        {
//            if ( i % 1000 == 0 && Gia_ObjRepr(p->pAig, i) )
//                Gia_ManEquivPrintOne( p->pAig, Gia_ObjRepr(p->pAig, i), 0 );
            if ( p->pPars->fColorDiff )
            {
                if ( !Gia_ObjDiffColors( p->pAig, Gia_ObjRepr(p->pAig, i), i ) )
                    continue;
            }
            else
            {
                if ( !Gia_ObjDiffColors2( p->pAig, Gia_ObjRepr(p->pAig, i), i ) )
                    continue;
            }
        }
        pRepr = Gia_ManObj( p->pAig, Gia_ObjRepr(p->pAig, i) );
        fCompl = Gia_ObjPhaseReal(pObj) ^ Gia_ObjPhaseReal(pRepr);
        // printf("iRepr %d\n", iRepr);
if(dtesting)    printf("piCopies[i]: %d -> ", piCopies[i]);
        piCopies[i] = Abc_LitNotCond( iRepr, fCompl );
if(dtesting)    printf(" %d\n", piCopies[i]);
// printf("8 p[%d]=%d\n", i, piCopies[i]);
        if ( Gia_ObjProved(p->pAig, i) )
            continue;
        // produce speculative miter
        iMiter = Gia_ManHashXor( pNew, iNode, piCopies[i] );
// printf("origin and %d&%d\n", toLitCond( Gia_ObjFaninId0(pObj,i), Gia_ObjFaninC0(pObj) ),  toLitCond( Gia_ObjFaninId1(pObj,i), Gia_ObjFaninC1(pObj) ));
// printf("2 p[%d]=%d %d&%d total: %d\n", i, piCopies[i], iRes0, iRes1 , Gia_ManAndNum(pNew));
        // printf("adding miter between node %d and %d\n", Abc_Lit2Var(iNode), Abc_Lit2Var(piCopies[i]));
if(dtesting)    printf("adding miter between %d(%d) and %d(%d)\n", iNode, Abc_Lit2Var(iNode), piCopies[i], Abc_Lit2Var(piCopies[i]));
        count1++;
        Gia_ManAppendCo( pNew, iMiter );
        Vec_IntPush( p->vXorNodes, Gia_ObjRepr(p->pAig, i) );
        Vec_IntPush( p->vXorNodes, i );
        // add to the depth of this node
        pDepths[i] = 1 + Abc_MaxInt( pDepths[i], pDepths[Gia_ObjRepr(p->pAig, i)] );
        if ( p->pPars->nDepthMax && pDepths[i] >= p->pPars->nDepthMax )
            piCopies[i] = -1;
    }
    // for(int i=0; i<Gia_ManObjNum(p->pAig); i++)
    //     printf("%d: %d\n", i, piCopies[i]);
    // count1 = count4
    // count3 is the times trying to adding iMiter, normally count3 > count1 = count4
    // if number of speculated const node is cst, the number of classes with i nodes is num[i]
    // count3 = cst + sigma( (i-1)*num[i] )
    if(testing) printf("    adding iMiter for %d times (trial: %d)\n", count1 , count3);
    if(testing) printf("    adding and for %d times\n", count2);
    if(testing) printf("<<<Cec_ManFraSpecReduction\n");
    ABC_FREE( piCopies );
    ABC_FREE( pDepths );
    Gia_ManHashStop( pNew );
    Gia_ManSetRegNum( pNew, 0 );
    // reduced below
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    Gia_ManPrintStats( pNew, NULL );
    return pNew;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManFraClassesUpdate_rec( Gia_Obj_t * pObj )
{
    int Result;
    if ( pObj->fMark0 )
        return 1;
    if ( Gia_ObjIsCi(pObj) || Gia_ObjIsConst0(pObj) )
        return 0;
    Result = (Cec_ManFraClassesUpdate_rec( Gia_ObjFanin0(pObj) ) |
              Cec_ManFraClassesUpdate_rec( Gia_ObjFanin1(pObj) ));
    return pObj->fMark0 = Result;
}

/**Function*************************************************************

  Synopsis    [Creates simulation info for this round.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManFraCreateInfo( Cec_ManSim_t * p, Vec_Ptr_t * vCiInfo, Vec_Ptr_t * vInfo, int nSeries )
{
    unsigned * pRes0, * pRes1;
    int i, w;
    for ( i = 0; i < Gia_ManCiNum(p->pAig); i++ )
    {
        pRes0 = (unsigned *)Vec_PtrEntry( vCiInfo, i );
        pRes1 = (unsigned *)Vec_PtrEntry( vInfo, i );
        pRes1 += p->nWords * nSeries;
        for ( w = 0; w < p->nWords; w++ )
            pRes0[w] = pRes1[w];
    }
}

/**Function*************************************************************

  Synopsis    [Updates equivalence classes using the patterns.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManFraClassesUpdate( Cec_ManFra_t * p, Cec_ManSim_t * pSim, Cec_ManPat_t * pPat, Gia_Man_t * pNew )
{
    Vec_Ptr_t * vInfo;
    Gia_Obj_t * pObj, * pObjOld, * pReprOld;
    int i, k, iRepr, iNode;
    int casep=0, cased=0, casef=0;
    abctime clk;
clk = Abc_Clock();
    vInfo = Cec_ManPatCollectPatterns( pPat, Gia_ManCiNum(p->pAig), pSim->nWords );
p->timePat += Abc_Clock() - clk;
clk = Abc_Clock();
    if ( vInfo != NULL )
    {
        Gia_ManCreateValueRefs( p->pAig );
        for ( i = 0; i < pPat->nSeries; i++ )
        {
            Cec_ManFraCreateInfo( pSim, pSim->vCiSimInfo, vInfo, i );
            if ( Cec_ManSimSimulateRound( pSim, pSim->vCiSimInfo, pSim->vCoSimInfo ) )
            {
                Vec_PtrFree( vInfo );
                return 1;
            }
        }
        Vec_PtrFree( vInfo );
    }
p->timeSim += Abc_Clock() - clk;
    assert( Vec_IntSize(p->vXorNodes) == 2*Gia_ManCoNum(pNew) );
    // mark the transitive fanout of failed nodes
    if ( p->pPars->nDepthMax != 1 )
    {
        Gia_ManCleanMark0( p->pAig );
        Gia_ManCleanMark1( p->pAig );
        Gia_ManForEachCo( pNew, pObj, k )
        {
            iRepr = Vec_IntEntry( p->vXorNodes, 2*k );
            iNode = Vec_IntEntry( p->vXorNodes, 2*k+1 );
            if ( pObj->fMark0 == 0 && pObj->fMark1 == 1 ) // proved
                continue;
//            Gia_ManObj(p->pAig, iRepr)->fMark0 = 1;
            Gia_ManObj(p->pAig, iNode)->fMark0 = 1;
        }
        // mark the nodes reachable through the failed nodes
        Gia_ManForEachAnd( p->pAig, pObjOld, k )
            pObjOld->fMark0 |= (Gia_ObjFanin0(pObjOld)->fMark0 | Gia_ObjFanin1(pObjOld)->fMark0);
        // unmark the disproved nodes
        Gia_ManForEachCo( pNew, pObj, k )
        {
            iRepr = Vec_IntEntry( p->vXorNodes, 2*k );
            iNode = Vec_IntEntry( p->vXorNodes, 2*k+1 );
            if ( pObj->fMark0 == 0 && pObj->fMark1 == 1 ) // proved
                continue; 
            pObjOld = Gia_ManObj(p->pAig, iNode);
            assert( pObjOld->fMark0 == 1 );
            if ( Gia_ObjFanin0(pObjOld)->fMark0 == 0 && Gia_ObjFanin1(pObjOld)->fMark0 == 0 )
                pObjOld->fMark1 = 1;
        }
        // clean marks
        Gia_ManForEachAnd( p->pAig, pObjOld, k )
            if ( pObjOld->fMark1 )
            {
                pObjOld->fMark0 = 0;
                pObjOld->fMark1 = 0;
            }
    }
    // set the results
    p->nAllProved = p->nAllDisproved = p->nAllFailed = 0;
    Gia_ManForEachCo( pNew, pObj, k )
    {
        iRepr = Vec_IntEntry( p->vXorNodes, 2*k );
        iNode = Vec_IntEntry( p->vXorNodes, 2*k+1 );
        pReprOld = Gia_ManObj(p->pAig, iRepr);
        pObjOld = Gia_ManObj(p->pAig, iNode);
        if ( pObj->fMark1 )
        { // proved
            casep++;
            assert( pObj->fMark0 == 0 );
            assert( !Gia_ObjProved(p->pAig, iNode) );
            if ( pReprOld->fMark0 == 0 && pObjOld->fMark0 == 0 )
//            if ( pObjOld->fMark0 == 0 )
            {
                assert( iRepr == Gia_ObjRepr(p->pAig, iNode) );
                Gia_ObjSetProved( p->pAig, iNode );
                p->nAllProved++;
            }
        }
        else if ( pObj->fMark0 )
        { // disproved
            cased++;
            assert( pObj->fMark1 == 0 );
            if ( pReprOld->fMark0 == 0 && pObjOld->fMark0 == 0 )
//            if ( pObjOld->fMark0 == 0 )
            {
                if ( iRepr == Gia_ObjRepr(p->pAig, iNode) )
                    Abc_Print( 1, "Cec_ManFraClassesUpdate(): Error! Node is not refined!\n" );
                p->nAllDisproved++;
            }
        }
        else
        { // failed
            casef++;
            assert( pObj->fMark0 == 0 );
            assert( pObj->fMark1 == 0 );
            assert( !Gia_ObjFailed(p->pAig, iNode) );
            assert( !Gia_ObjProved(p->pAig, iNode) );
            Gia_ObjSetFailed( p->pAig, iNode );
            p->nAllFailed++;
        }
    } 
    // printf("! %d %d %d %d\n\n", k, p->nAllProved, p->nAllDisproved, p->nAllFailed);
    // printf("! %d %d %d %d\n\n", k, casep, cased, casef);
    p->nAllProvedS    += p->nAllProved;
    p->nAllDisprovedS += p->nAllDisproved;
    p->nAllFailedS    += p->nAllFailed;
    return 0;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

