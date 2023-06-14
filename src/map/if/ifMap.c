/**CFile****************************************************************

  FileName    [ifMap.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [FPGA mapping based on priority cuts.]

  Synopsis    [Mapping procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 21, 2006.]

  Revision    [$Id: ifMap.c,v 1.00 2006/11/21 00:00:00 alanmi Exp $]

***********************************************************************/

#include "if.h"
#include "misc/extra/extra.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

extern char * Dau_DsdMerge( char * pDsd0i, int * pPerm0, char * pDsd1i, int * pPerm1, int fCompl0, int fCompl1, int nVars );
extern int    If_CutDelayRecCost3( If_Man_t* p, If_Cut_t* pCut, If_Obj_t * pObj );
extern int    Abc_ExactDelayCost( word * pTruth, int nVars, int * pArrTimeProfile, char * pPerm, int * Cost, int AigLevel );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Compute delay of the cut's output in terms of logic levels.]

  Description [Uses the best arrival time of the fanins of the cut
  to compute the arrival times of the output of the cut.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_ManCutAigDelay_rec( If_Man_t * p, If_Obj_t * pObj, Vec_Ptr_t * vVisited )
{
    int Delay0, Delay1;
    if ( pObj->fVisit )
        return pObj->iCopy;
    if ( If_ObjIsCi(pObj) || If_ObjIsConst1(pObj) )
        return -1;
    // store the node in the structure by level
    assert( If_ObjIsAnd(pObj) );
    pObj->fVisit = 1;
    Vec_PtrPush( vVisited, pObj );
    Delay0 = If_ManCutAigDelay_rec( p, pObj->pFanin0, vVisited );
    Delay1 = If_ManCutAigDelay_rec( p, pObj->pFanin1, vVisited );
    pObj->iCopy = (Delay0 >= 0 && Delay1 >= 0) ? 1 + Abc_MaxInt(Delay0, Delay1) : -1;
    return pObj->iCopy;
}
int If_ManCutAigDelay( If_Man_t * p, If_Obj_t * pObj, If_Cut_t * pCut )
{
    If_Obj_t * pLeaf;
    int i, Delay;
    Vec_PtrClear( p->vVisited );
    If_CutForEachLeaf( p, pCut, pLeaf, i )
    {
        assert( pLeaf->fVisit == 0 );
        pLeaf->fVisit = 1;
        Vec_PtrPush( p->vVisited, pLeaf );
        pLeaf->iCopy = If_ObjCutBest(pLeaf)->Delay;
    }
    Delay = If_ManCutAigDelay_rec( p, pObj, p->vVisited );
    Vec_PtrForEachEntry( If_Obj_t *, p->vVisited, pLeaf, i )
        pLeaf->fVisit = 0;
//    assert( Delay <= (int)pObj->Level );
    return Delay;
}

/**Function*************************************************************

  Synopsis    [Counts the number of 1s in the signature.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int If_WordCountOnes( unsigned uWord )
{
    uWord = (uWord & 0x55555555) + ((uWord>>1) & 0x55555555);
    uWord = (uWord & 0x33333333) + ((uWord>>2) & 0x33333333);
    uWord = (uWord & 0x0F0F0F0F) + ((uWord>>4) & 0x0F0F0F0F);
    uWord = (uWord & 0x00FF00FF) + ((uWord>>8) & 0x00FF00FF);
    return  (uWord & 0x0000FFFF) + (uWord>>16);
}

/**Function*************************************************************

  Synopsis    [Counts the number of 1s in the signature.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
float If_CutDelaySpecial( If_Man_t * p, If_Cut_t * pCut, int fCarry )
{
    static float Pin2Pin[2][3] = { {1.0, 1.0, 1.0}, {1.0, 1.0, 0.0} };
    If_Obj_t * pLeaf;
    float DelayCur, Delay = -IF_FLOAT_LARGE;
    int i;
    assert( pCut->nLeaves <= 3 );
    If_CutForEachLeaf( p, pCut, pLeaf, i )
    {
        DelayCur = If_ObjCutBest(pLeaf)->Delay;
        Delay = IF_MAX( Delay, Pin2Pin[fCarry][i] + DelayCur );
    }
    return Delay;
}

/**Function*************************************************************

  Synopsis    [Returns arrival time profile of the cut.]

  Description [The procedure returns static storage, which should not be
  deallocated and is only valid until before the procedure is called again.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int * If_CutArrTimeProfile( If_Man_t * p, If_Cut_t * pCut )
{
    int i;
    for ( i = 0; i < If_CutLeaveNum(pCut); i++ )
        p->pArrTimeProfile[i] = (int)If_ObjCutBest(If_CutLeaf(p, pCut, i))->Delay;
    return p->pArrTimeProfile;
}

/**Function*************************************************************

  Synopsis    [Finds the best cut for the given node.]

  Description [Mapping modes: delay (0), area flow (1), area (2).]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void If_ObjPerformMappingAnd( If_Man_t * p, If_Obj_t * pObj, int Mode, int fPreprocess, int fFirst )
{
    If_Set_t * pCutSet;
    If_Cut_t * pCut0, * pCut1, * pCut;
    If_Cut_t * pCut0R, * pCut1R;
    int fFunc0R, fFunc1R;
    int i, k, v, iCutDsd, fChange;
    int fSave0 = p->pPars->fDelayOpt || p->pPars->fDelayOptLut || p->pPars->fDsdBalance || p->pPars->fUserRecLib || p->pPars->fUserSesLib || 
        p->pPars->fUseDsdTune || p->pPars->fUseCofVars || p->pPars->fUseAndVars || p->pPars->fUse34Spec || p->pPars->pLutStruct || p->pPars->pFuncCell2 || p->pPars->fUseCheck1 || p->pPars->fUseCheck2;
    int fUseAndCut = (p->pPars->nAndDelay > 0) || (p->pPars->nAndArea > 0);
    assert( !If_ObjIsAnd(pObj->pFanin0) || pObj->pFanin0->pCutSet->nCuts > 0 );
    assert( !If_ObjIsAnd(pObj->pFanin1) || pObj->pFanin1->pCutSet->nCuts > 0 );

    // prepare
    if ( Mode == 0 )
        pObj->EstRefs = (float)pObj->nRefs;
    else if ( Mode == 1 )
        pObj->EstRefs = (float)((2.0 * pObj->EstRefs + pObj->nRefs) / 3.0);
    // deref the selected cut
    if ( Mode && pObj->nRefs > 0 )
        If_CutAreaDeref( p, If_ObjCutBest(pObj) );

    // prepare the cutset
    pCutSet = If_ManSetupNodeCutSet( p, pObj );

    // get the current assigned best cut
    pCut = If_ObjCutBest(pObj);
    if ( !fFirst )
    {
        // recompute the parameters of the best cut
        if ( p->pPars->fUserRecLib )
            pCut->Delay = If_CutDelayRecCost3( p, pCut, pObj ); 
        else
            pCut->Delay = If_CutDelay( p, pObj, pCut );
        assert( pCut->Delay != -1 );
//        assert( pCut->Delay <= pObj->Required + p->fEpsilon );
        if ( pCut->Delay > pObj->Required + 2*p->fEpsilon )
            Abc_Print( 1, "If_ObjPerformMappingAnd(): Warning! Node with ID %d has delay (%f) exceeding the required times (%f).\n", 
                pObj->Id, pCut->Delay, pObj->Required + p->fEpsilon );
        pCut->Area = (Mode == 2)? If_CutAreaDerefed( p, pCut ) : If_CutAreaFlow( p, pCut );
        // save the best cut from the previous iteration
        if ( !fPreprocess || pCut->nLeaves <= 1 )
            If_CutCopy( p, pCutSet->ppCuts[pCutSet->nCuts++], pCut );
    }   // if ( !fFirst )
// printf("cuts of nodeId: %d \n", pObj->Id);
    // generate cuts
    If_ObjForEachCut( pObj->pFanin0, pCut0, i )
    If_ObjForEachCut( pObj->pFanin1, pCut1, k )
    // for ( k = 0; (k < (pObj->pFanin1)->pCutSet->nCuts) && ((pCut1) = (pObj->pFanin1)->pCutSet->ppCuts[k]); k++ )
    {
        // get the next free cut
        assert( pCutSet->nCuts <= pCutSet->nCutsMax );
        pCut = pCutSet->ppCuts[pCutSet->nCuts];
        // make sure K-feasible cut exists
        if ( If_WordCountOnes(pCut0->uSign | pCut1->uSign) > p->pPars->nLutSize )
            continue;      

        // // merge the cuts
        if ( !If_CutMergeOrdered( p, pCut0, pCut1, pCut ) )
            continue;
        
        // if ( pObj->fSpec && pCut->nLeaves == (unsigned)p->pPars->nLutSize )
        //     continue;
        p->nCutsMerged++;
        p->nCutsTotal++;
        // check if this cut is contained in any of the available cuts
        if ( !p->pPars->fSkipCutFilter && If_CutFilter( pCutSet, pCut, fSave0 ) )
            continue;
        // check if the cut is a special AND-gate cut
        pCut->fAndCut = fUseAndCut && pCut->nLeaves == 2 && pCut->pLeaves[0] == pObj->pFanin0->Id && pCut->pLeaves[1] == pObj->pFanin1->Id;

        // compute the truth table
        pCut->iCutFunc = -1;
        pCut->fCompl = 0;
        if ( p->pPars->fTruth )
        {
//            int nShared = pCut0->nLeaves + pCut1->nLeaves - pCut->nLeaves;
            abctime clk = 0;
            fChange = If_CutComputeTruth( p, pCut, pCut0, pCut1, pObj->fCompl0, pObj->fCompl1 );
            if ( p->pPars->fVerbose )
                p->timeCache[4] += Abc_Clock() - clk;
            if ( !p->pPars->fSkipCutFilter && fChange && If_CutFilter( pCutSet, pCut, fSave0 ) )
                continue;
            if ( p->pPars->fLut6Filter && pCut->nLeaves == 6 && !If_CutCheckTruth6(p, pCut) )
                continue;

            // run user functions
            pCut->fUseless = 0;

        }
        
        // compute the application-specific cost and depth
        pCut->fUser = (p->pPars->pFuncCost != NULL);
        pCut->Cost = p->pPars->pFuncCost? p->pPars->pFuncCost(p, pCut) : 0;
        if ( pCut->Cost == IF_COST_MAX )
            continue;
        // check if the cut satisfies the required times
        if ( p->pPars->fUserRecLib )
            pCut->Delay = If_CutDelayRecCost3( p, pCut, pObj ); 
        else 
            pCut->Delay = If_CutDelay( p, pObj, pCut );
        if ( pCut->Delay == -1 )
            continue;
        if ( Mode && pCut->Delay > pObj->Required + p->fEpsilon )
            continue;
        // compute area of the cut (this area may depend on the application specific cost)
        pCut->Area = (Mode == 2)? If_CutAreaDerefed( p, pCut ) : If_CutAreaFlow( p, pCut );

        If_CutSort( p, pCutSet, pCut );
    }   // traverse all cuts combinations of two fanins
    assert( pCutSet->nCuts > 0 );
// printf("\n");
    // update the best cut
    if ( !fPreprocess || pCutSet->ppCuts[0]->Delay <= pObj->Required + p->fEpsilon )
    {
        If_CutCopy( p, If_ObjCutBest(pObj), pCutSet->ppCuts[0] );
        if ( p->pPars->fUserRecLib || p->pPars->fUserSesLib )
            assert(If_ObjCutBest(pObj)->Cost < IF_COST_MAX && If_ObjCutBest(pObj)->Delay < ABC_INFINITY);
    }
    // add the trivial cut to the set
    if ( !pObj->fSkipCut && If_ObjCutBest(pObj)->nLeaves > 1 )
    {
        If_ManSetupCutTriv( p, pCutSet->ppCuts[pCutSet->nCuts++], pObj->Id );
        assert( pCutSet->nCuts <= pCutSet->nCutsMax+1 );
    }

    // ref the selected cut
    if ( Mode && pObj->nRefs > 0 )
        If_CutAreaRef( p, If_ObjCutBest(pObj) );
    if ( If_ObjCutBest(pObj)->fUseless )
        Abc_Print( 1, "The best cut is useless.\n" );

    // free the cuts
    If_ManDerefNodeCutSet( p, pObj );
}

/**Function*************************************************************

  Synopsis    [Finds the best cut for the choice node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void If_ObjPerformMappingChoice( If_Man_t * p, If_Obj_t * pObj, int Mode, int fPreprocess ){}

/**Function*************************************************************

  Synopsis    [Performs one mapping pass over all nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
extern int getInternalNode( If_Man_t * pIfMan, If_Obj_t * pObj, If_Cut_t * pCut, int * pBestPo);
int If_ManPerformMappingRound( If_Man_t * p, int nCutsUsed, int Mode, int fPreprocess, int fFirst, char * pLabel )
{
    ProgressBar * pProgress = NULL;
    If_Obj_t * pObj;
    int i;
    abctime clk = Abc_Clock();
    float arrTime;
    assert( Mode >= 0 && Mode <= 2 );
    p->nBestCutSmall[0] = p->nBestCutSmall[1] = 0;
    // set the sorting function
    if ( Mode || p->pPars->fArea ) // area
        p->SortMode = 1;
    else if ( p->pPars->fFancy )
        p->SortMode = 2;
    else
        p->SortMode = 0;
    // set the cut number
    p->nCutsUsed   = nCutsUsed;
    p->nCutsMerged = 0;
    // make sure the visit counters are all zero
    If_ManForEachNode( p, pObj, i )
        assert( pObj->nVisits == pObj->nVisitsCopy );
    // map the internal nodes
    // default here
    pProgress = Extra_ProgressBarStart( stdout, If_ManObjNum(p) );
    If_ManForEachNode( p, pObj, i )
    {
        Extra_ProgressBarUpdate( pProgress, i, pLabel );
        If_ObjPerformMappingAnd( p, pObj, Mode, fPreprocess, fFirst );

    }
    
    Extra_ProgressBarStop( pProgress );
    // make sure the visit counters are all zero
    If_ManForEachNode( p, pObj, i )
        assert( pObj->nVisits == 0 );
    // compute required times and stats
    If_ManComputeRequired( p );
//    Tim_ManPrint( p->pManTim );
    if ( p->pPars->fVerbose )
    {
        char Symb = fPreprocess? 'P' : ((Mode == 0)? 'D' : ((Mode == 1)? 'F' : 'A'));
        Abc_Print( 1, "%c:  Del = %7.2f.  Ar = %9.1f.  Edge = %8d.  ", 
            Symb, p->RequiredGlo, p->AreaGlo, p->nNets );
        if ( p->dPower )
            Abc_Print( 1, "Switch = %7.2f.  ", p->dPower );
        Abc_Print( 1, "Cut = %8d.  ", p->nCutsMerged );
        Abc_PrintTime( 1, "T", Abc_Clock() - clk );
//    Abc_Print( 1, "Max number of cuts = %d. Average number of cuts = %5.2f.\n", 
//        p->nCutsMax, 1.0 * p->nCutsMerged / If_ManAndNum(p) );
    }

    int printBestStructure = 1;
    if(printBestStructure){
        printf("printBestStructure\n");
        If_Obj_t * pIfObj;
        If_Cut_t * pCutBest;
        int total_area=0;
        If_ManForEachNode( p, pIfObj, i )
        {
            if ( pIfObj->nRefs == 0 && !If_ObjIsTerm(pIfObj) )
                continue;
            if ( If_ObjIsAnd(pIfObj) ){
                int BestPo = -1;
                pCutBest = If_ObjCutBest( pIfObj );
                int s = getInternalNode(p, pIfObj, pCutBest, &BestPo);
                printf("(%d %d %d %.2lf) ", i, BestPo, s, pCutBest->Area);
                total_area += s;
            }
        }
        printf("\narea upper_bound: %d\n", total_area);
    }


    return 1;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

