/**CFile****************************************************************

  FileName    [cecSolve.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Combinational equivalence checking.]

  Synopsis    [Performs one round of SAT solving.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: cecSolve.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cecInt.h"
#include <pthread.h>

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static inline int  Cec_ObjSatNum( Cec_ManSat_t * p, Gia_Obj_t * pObj )             { return p->pSatVars[Gia_ObjId(p->pAig,pObj)]; }
static inline void Cec_ObjSetSatNum( Cec_ManSat_t * p, Gia_Obj_t * pObj, int Num ) { p->pSatVars[Gia_ObjId(p->pAig,pObj)] = Num;  }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Returns value of the SAT variable.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ObjSatVarValue( Cec_ManSat_t * p, Gia_Obj_t * pObj )             
{ 
//     static inline int sat_solver_var_value( sat_solver* s, int v )
// {
//     assert( v >= 0 && v < s->size );
//     return (int)(s->model[v] == l_True);
// }
    return sat_solver_var_value( p->pSat, Cec_ObjSatNum(p, pObj) );
}

/**Function*************************************************************

  Synopsis    [Addes clauses to the solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_AddClausesMux( Cec_ManSat_t * p, Gia_Obj_t * pNode )
{
    Gia_Obj_t * pNodeI, * pNodeT, * pNodeE;
    int pLits[4], RetValue, VarF, VarI, VarT, VarE, fCompT, fCompE;

    assert( !Gia_IsComplement( pNode ) );
    assert( Gia_ObjIsMuxType( pNode ) );
    // get nodes (I = if, T = then, E = else)
    pNodeI = Gia_ObjRecognizeMux( pNode, &pNodeT, &pNodeE );
    // get the variable numbers
    VarF = Cec_ObjSatNum(p,pNode);
    VarI = Cec_ObjSatNum(p,pNodeI);
    VarT = Cec_ObjSatNum(p,Gia_Regular(pNodeT));
    VarE = Cec_ObjSatNum(p,Gia_Regular(pNodeE));
    // get the complementation flags
    fCompT = Gia_IsComplement(pNodeT);
    fCompE = Gia_IsComplement(pNodeE);

    // f = ITE(i, t, e)

    // i' + t' + f
    // i' + t  + f'
    // i  + e' + f
    // i  + e  + f'

    // create four clauses
    pLits[0] = toLitCond(VarI, 1);
    pLits[1] = toLitCond(VarT, 1^fCompT);
    pLits[2] = toLitCond(VarF, 0);
    if ( p->pPars->fPolarFlip )
    {
        if ( pNodeI->fPhase )               pLits[0] = lit_neg( pLits[0] );
        if ( Gia_Regular(pNodeT)->fPhase )  pLits[1] = lit_neg( pLits[1] );
        if ( pNode->fPhase )                pLits[2] = lit_neg( pLits[2] );
    }
    RetValue = sat_solver_addclause( p->pSat, pLits, pLits + 3 );
    assert( RetValue );
    pLits[0] = toLitCond(VarI, 1);
    pLits[1] = toLitCond(VarT, 0^fCompT);
    pLits[2] = toLitCond(VarF, 1);
    if ( p->pPars->fPolarFlip )
    {
        if ( pNodeI->fPhase )               pLits[0] = lit_neg( pLits[0] );
        if ( Gia_Regular(pNodeT)->fPhase )  pLits[1] = lit_neg( pLits[1] );
        if ( pNode->fPhase )                pLits[2] = lit_neg( pLits[2] );
    }
    RetValue = sat_solver_addclause( p->pSat, pLits, pLits + 3 );
    assert( RetValue );
    pLits[0] = toLitCond(VarI, 0);
    pLits[1] = toLitCond(VarE, 1^fCompE);
    pLits[2] = toLitCond(VarF, 0);
    if ( p->pPars->fPolarFlip )
    {
        if ( pNodeI->fPhase )               pLits[0] = lit_neg( pLits[0] );
        if ( Gia_Regular(pNodeE)->fPhase )  pLits[1] = lit_neg( pLits[1] );
        if ( pNode->fPhase )                pLits[2] = lit_neg( pLits[2] );
    }
    RetValue = sat_solver_addclause( p->pSat, pLits, pLits + 3 );
    assert( RetValue );
    pLits[0] = toLitCond(VarI, 0);
    pLits[1] = toLitCond(VarE, 0^fCompE);
    pLits[2] = toLitCond(VarF, 1);
    if ( p->pPars->fPolarFlip )
    {
        if ( pNodeI->fPhase )               pLits[0] = lit_neg( pLits[0] );
        if ( Gia_Regular(pNodeE)->fPhase )  pLits[1] = lit_neg( pLits[1] );
        if ( pNode->fPhase )                pLits[2] = lit_neg( pLits[2] );
    }
    RetValue = sat_solver_addclause( p->pSat, pLits, pLits + 3 );
    assert( RetValue );

    // two additional clauses
    // t' & e' -> f'
    // t  & e  -> f 

    // t  + e   + f'
    // t' + e'  + f 

    if ( VarT == VarE )
    {
//        assert( fCompT == !fCompE );
        return;
    }

    pLits[0] = toLitCond(VarT, 0^fCompT);
    pLits[1] = toLitCond(VarE, 0^fCompE);
    pLits[2] = toLitCond(VarF, 1);
    if ( p->pPars->fPolarFlip )
    {
        if ( Gia_Regular(pNodeT)->fPhase )  pLits[0] = lit_neg( pLits[0] );
        if ( Gia_Regular(pNodeE)->fPhase )  pLits[1] = lit_neg( pLits[1] );
        if ( pNode->fPhase )                pLits[2] = lit_neg( pLits[2] );
    }
    RetValue = sat_solver_addclause( p->pSat, pLits, pLits + 3 );
    assert( RetValue );
    pLits[0] = toLitCond(VarT, 1^fCompT);
    pLits[1] = toLitCond(VarE, 1^fCompE);
    pLits[2] = toLitCond(VarF, 0);
    if ( p->pPars->fPolarFlip )
    {
        if ( Gia_Regular(pNodeT)->fPhase )  pLits[0] = lit_neg( pLits[0] );
        if ( Gia_Regular(pNodeE)->fPhase )  pLits[1] = lit_neg( pLits[1] );
        if ( pNode->fPhase )                pLits[2] = lit_neg( pLits[2] );
    }
    RetValue = sat_solver_addclause( p->pSat, pLits, pLits + 3 );
    assert( RetValue );
}

/**Function*************************************************************

  Synopsis    [Addes clauses to the solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_AddClausesSuper( Cec_ManSat_t * p, Gia_Obj_t * pNode, Vec_Ptr_t * vSuper )
{
    Gia_Obj_t * pFanin;
    int * pLits, nLits, RetValue, i;
    assert( !Gia_IsComplement(pNode) );
    assert( Gia_ObjIsAnd( pNode ) );
    // create storage for literals
    nLits = Vec_PtrSize(vSuper) + 1;
    pLits = ABC_ALLOC( int, nLits );
    // for an AND-gate A & B = C
    // !A => !C   A + !C
    // !B => !C   B + !C
    // for A & B & C = D
    // A + !D  B + !D  C + !D
    Vec_PtrForEachEntry( Gia_Obj_t *, vSuper, pFanin, i )
    {
        pLits[0] = toLitCond(Cec_ObjSatNum(p,Gia_Regular(pFanin)), Gia_IsComplement(pFanin));
        pLits[1] = toLitCond(Cec_ObjSatNum(p,pNode), 1);
        if ( p->pPars->fPolarFlip )
        {
            if ( Gia_Regular(pFanin)->fPhase )  pLits[0] = lit_neg( pLits[0] );
            if ( pNode->fPhase )                pLits[1] = lit_neg( pLits[1] );
        }
        RetValue = sat_solver_addclause( p->pSat, pLits, pLits + 2 );
        assert( RetValue );
    }
    Vec_PtrForEachEntry( Gia_Obj_t *, vSuper, pFanin, i )
    {
        pLits[i] = toLitCond(Cec_ObjSatNum(p,Gia_Regular(pFanin)), !Gia_IsComplement(pFanin));
        if ( p->pPars->fPolarFlip )
        {
            if ( Gia_Regular(pFanin)->fPhase )  pLits[i] = lit_neg( pLits[i] );
        }
    }
    pLits[nLits-1] = toLitCond(Cec_ObjSatNum(p,pNode), 0);
    if ( p->pPars->fPolarFlip )
    {
        if ( pNode->fPhase )  pLits[nLits-1] = lit_neg( pLits[nLits-1] );
    }
    // A & B => C   or   !A + !B + C
    // !A + !B + !C + D
    RetValue = sat_solver_addclause( p->pSat, pLits, pLits + nLits );
    assert( RetValue );
    ABC_FREE( pLits );
}

/**Function*************************************************************

  Synopsis    [Collects the supergate.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_CollectSuper_rec( Gia_Obj_t * pObj, Vec_Ptr_t * vSuper, int fFirst, int fUseMuxes )
{
    // if the new node is complemented or a PI, another gate begins
    if ( Gia_IsComplement(pObj) || Gia_ObjIsCi(pObj) || 
         (!fFirst && Gia_ObjValue(pObj) > 1) || 
         (fUseMuxes && Gia_ObjIsMuxType(pObj)) )
    {
        Vec_PtrPushUnique( vSuper, pObj );
        return;
    }
    // go through the branches
    Cec_CollectSuper_rec( Gia_ObjChild0(pObj), vSuper, 0, fUseMuxes );
    Cec_CollectSuper_rec( Gia_ObjChild1(pObj), vSuper, 0, fUseMuxes );
}

/**Function*************************************************************

  Synopsis    [Collects the supergate.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_CollectSuper( Gia_Obj_t * pObj, int fUseMuxes, Vec_Ptr_t * vSuper )
{
    assert( !Gia_IsComplement(pObj) );
    assert( !Gia_ObjIsCi(pObj) );
    Vec_PtrClear( vSuper );
    Cec_CollectSuper_rec( pObj, vSuper, 1, fUseMuxes );
}

/**Function*************************************************************

  Synopsis    [Updates the solver clause database.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ObjAddToFrontier( Cec_ManSat_t * p, Gia_Obj_t * pObj, Vec_Ptr_t * vFrontier )
{
    assert( !Gia_IsComplement(pObj) );
    if ( Cec_ObjSatNum(p,pObj) )
        return;
    assert( Cec_ObjSatNum(p,pObj) == 0 );
    if ( Gia_ObjIsConst0(pObj) )
        return;
    Vec_PtrPush( p->vUsedNodes, pObj );
    Cec_ObjSetSatNum( p, pObj, p->nSatVars++ );
    if ( Gia_ObjIsAnd(pObj) )
        Vec_PtrPush( vFrontier, pObj );
}

/**Function*************************************************************

  Synopsis    [Updates the solver clause database.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_CnfNodeAddToSolver( Cec_ManSat_t * p, Gia_Obj_t * pObj )
{ 
    lbool testing = false;
    Vec_Ptr_t * vFrontier;
    Gia_Obj_t * pNode, * pFanin;
    int i, k, fUseMuxes = 1;
    // quit if CNF is ready
    if ( Cec_ObjSatNum(p,pObj) )
        return;
    if ( Gia_ObjIsCi(pObj) )
    {
        Vec_PtrPush( p->vUsedNodes, pObj );
        Cec_ObjSetSatNum( p, pObj, p->nSatVars++ );
        sat_solver_setnvars( p->pSat, p->nSatVars );
        return;
    }
    assert( Gia_ObjIsAnd(pObj) );
    // start the frontier
    vFrontier = Vec_PtrAlloc( 100 );
    Cec_ObjAddToFrontier( p, pObj, vFrontier );
    int before_clauses = p->pSat->stats.clauses;
    long before_lits = p->pSat->stats.clauses_literals;
    if(testing) printf("    >>>> Cec_CnfNodeAddToSolver cl: %d lit: %ld \n",   p->pSat->stats.clauses, p->pSat->stats.clauses_literals);
    // if(testing) printf("    vFrontire size %d cap %d\n", vFrontier->nSize, vFrontier->nCap);
    // explore nodes in the frontier
    // Vec_PtrForEachEntry( Gia_Obj_t *, vFrontier, pNode, i )
    for ( i = 0; (i < Vec_PtrSize(vFrontier)) && (((pNode) = (Gia_Obj_t *)Vec_PtrEntry(vFrontier, i)), 1); i++ )
    {
        // printf("    frontier is and? %s\n", Gia_ObjIsAnd(pNode)?"yes":"no" ); // always yes
        if(testing) printf("        pNodeId: %d\n", Gia_ObjId(p->pAig, pNode));
        // create the supergate
        assert( Cec_ObjSatNum(p,pNode) );
        int sub_before_clauses = p->pSat->stats.clauses;
        long sub_before_lits = p->pSat->stats.clauses_literals;
        if ( fUseMuxes && Gia_ObjIsMuxType(pNode) )
        {
            Vec_PtrClear( p->vFanins );
            Vec_PtrPushUnique( p->vFanins, Gia_ObjFanin0( Gia_ObjFanin0(pNode) ) );
            Vec_PtrPushUnique( p->vFanins, Gia_ObjFanin0( Gia_ObjFanin1(pNode) ) );
            Vec_PtrPushUnique( p->vFanins, Gia_ObjFanin1( Gia_ObjFanin0(pNode) ) );
            Vec_PtrPushUnique( p->vFanins, Gia_ObjFanin1( Gia_ObjFanin1(pNode) ) );
            Vec_PtrForEachEntry( Gia_Obj_t *, p->vFanins, pFanin, k )
            // for ( k = 0; (k < Vec_PtrSize(p->vFanins)) && (((pFanin) = (Gia_Obj_t *)Vec_PtrEntry(p->vFanins, k)), 1); k++ )
                Cec_ObjAddToFrontier( p, Gia_Regular(pFanin), vFrontier );
            Cec_AddClausesMux( p, pNode );
            if(testing) printf("            add1 cl: %d -> %d lit: %ld -> %ld \n",   sub_before_clauses, p->pSat->stats.clauses, sub_before_lits, p->pSat->stats.clauses_literals);
        }
        else
        {
            Cec_CollectSuper( pNode, fUseMuxes, p->vFanins );
            Vec_PtrForEachEntry( Gia_Obj_t *, p->vFanins, pFanin, k )
                Cec_ObjAddToFrontier( p, Gia_Regular(pFanin), vFrontier );
            Cec_AddClausesSuper( p, pNode, p->vFanins );
            if(testing) printf("            add2 cl: %d -> %d lit: %ld -> %ld \n",   sub_before_clauses, p->pSat->stats.clauses, sub_before_lits, p->pSat->stats.clauses_literals);
        }
        assert( Vec_PtrSize(p->vFanins) > 1 );
    }
    if(testing) printf("    <<<< Cec_CnfNodeAddToSolver cl: %d -> %d  lit: %ld -> %ld\n",   
        before_clauses, p->pSat->stats.clauses, before_lits, p->pSat->stats.clauses_literals);
    Vec_PtrFree( vFrontier );
}


/**Function*************************************************************

  Synopsis    [Recycles the SAT solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManSatSolverRecycle( Cec_ManSat_t * p )
{
    int Lit;
    if ( p->pSat )
    {
        Gia_Obj_t * pObj;
        int i;
        Vec_PtrForEachEntry( Gia_Obj_t *, p->vUsedNodes, pObj, i )
            Cec_ObjSetSatNum( p, pObj, 0 );
        Vec_PtrClear( p->vUsedNodes );
//        memset( p->pSatVars, 0, sizeof(int) * Gia_ManObjNumMax(p->pAigTotal) );
        sat_solver_delete( p->pSat );
    }
    p->pSat = sat_solver_new();
    sat_solver_setnvars( p->pSat, 1000 );
    p->pSat->factors = ABC_CALLOC( double, p->pSat->cap );
    // var 0 is not used
    // var 1 is reserved for const0 node - add the clause
    p->nSatVars = 1;
//    p->nSatVars = 0;
    Lit = toLitCond( p->nSatVars, 1 );
//    if ( p->pPars->fPolarFlip ) // no need to normalize const0 node (bug fix by SS on 9/17/2012)
//        Lit = lit_neg( Lit );
    sat_solver_addclause( p->pSat, &Lit, &Lit + 1 );
    Cec_ObjSetSatNum( p, Gia_ManConst0(p->pAig), p->nSatVars++ );

    p->nRecycles++;
    p->nCallsSince = 0;
}

/**Function*************************************************************

  Synopsis    [Sets variable activities in the cone.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_SetActivityFactors_rec( Cec_ManSat_t * p, Gia_Obj_t * pObj, int LevelMin, int LevelMax )
{
    float dActConeBumpMax = 20.0;
    int iVar;
    // skip visited variables
    if ( Gia_ObjIsTravIdCurrent(p->pAig, pObj) )
        return;
    Gia_ObjSetTravIdCurrent(p->pAig, pObj);
    // add the PI to the list
    if ( Gia_ObjLevel(p->pAig, pObj) <= LevelMin || Gia_ObjIsCi(pObj) )
        return;
    // set the factor of this variable
    // (LevelMax-LevelMin) / (pObj->Level-LevelMin) = p->pPars->dActConeBumpMax / ThisBump
    if ( (iVar = Cec_ObjSatNum(p,pObj)) )
    {
        p->pSat->factors[iVar] = dActConeBumpMax * (Gia_ObjLevel(p->pAig, pObj) - LevelMin)/(LevelMax - LevelMin);
        veci_push(&p->pSat->act_vars, iVar);
    }
    // explore the fanins
    Cec_SetActivityFactors_rec( p, Gia_ObjFanin0(pObj), LevelMin, LevelMax );
    Cec_SetActivityFactors_rec( p, Gia_ObjFanin1(pObj), LevelMin, LevelMax );
}

/**Function*************************************************************

  Synopsis    [Sets variable activities in the cone.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_SetActivityFactors( Cec_ManSat_t * p, Gia_Obj_t * pObj )
{
    float dActConeRatio = 0.5;
    int LevelMin, LevelMax;
    // reset the active variables
    veci_resize(&p->pSat->act_vars, 0);
    // prepare for traversal
    Gia_ManIncrementTravId( p->pAig );
    // determine the min and max level to visit
    assert( dActConeRatio > 0 && dActConeRatio < 1 );
    LevelMax = Gia_ObjLevel(p->pAig,pObj);
    LevelMin = (int)(LevelMax * (1.0 - dActConeRatio));
    // traverse
    Cec_SetActivityFactors_rec( p, pObj, LevelMin, LevelMax );
//Cec_PrintActivity( p );
    return 1;
}


/**Function*************************************************************

  Synopsis    [Runs equivalence test for the two nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
// pObj = child0(co)
// return 1 for UNSAT, 0 for SAT, -1 for UNDET
int Cec_ManSatCheckNode( Cec_ManSat_t * p, Gia_Obj_t * pObj )
{
    // for testing **
    // Abc_Print( 1, "Enter cecSolve.c/Cec_ManSatCheckNode()\n" );
    // printf("    >>> sat_solver_addclause %.1f %.1f \n",   (double)p->pSat->stats.clauses, (double)p->pSat->stats.clauses_literals);
    lbool testing = false;
    // printf("call Cec_ManSatCheckNode at %p\n", p);

    Gia_Obj_t * pObjR = Gia_Regular(pObj);
    int nBTLimit = p->pPars->nBTLimit;
    int Lit, RetValue, status, nConflicts;
    abctime clk, clk2;

    if ( pObj == Gia_ManConst0(p->pAig) )
        return 1;
    if ( pObj == Gia_ManConst1(p->pAig) )
    {
        assert( 0 );
        return 0;
    }

    p->nCallsSince++;  // experiment with this!!!
    p->nSatTotal++;
    
    // check if SAT solver needs recycling
    if ( p->pSat == NULL || 
        (p->pPars->nSatVarMax && 
         p->nSatVars > p->pPars->nSatVarMax && 
         p->nCallsSince > p->pPars->nCallsRecycle) )
        Cec_ManSatSolverRecycle( p );

    // if the nodes do not have SAT variables, allocate them
clk2 = Abc_Clock();

    if(testing) printf("    before ManSatCheckNode #cl: %d #lit: %ld \n",   p->pSat->stats.clauses, p->pSat->stats.clauses_literals);
    // clauses and literals are mostly added here
    Cec_CnfNodeAddToSolver( p, pObjR );   
    if(testing) printf("    after ManSatCheckNode #cl: %d #lit: %ld \n",   p->pSat->stats.clauses, p->pSat->stats.clauses_literals);
    if(testing) printf("    ManSatCheckNode pObjRId %d Lit%d\n", Gia_ObjId(p->pAig, pObjR), toLitCond( Cec_ObjSatNum(p,pObjR), Gia_IsComplement(pObj) )); 
//ABC_PRT( "cnf", Abc_Clock() - clk2 );
// Abc_Print( 1, "%d \n", p->pSat->size );

clk2 = Abc_Clock();
//    Cec_SetActivityFactors( p, pObjR ); 
//ABC_PRT( "act", Abc_Clock() - clk2 );

    // propage unit clauses
    if ( p->pSat->qtail != p->pSat->qhead )
    {
        status = sat_solver_simplify(p->pSat);
        assert( status != 0 );
        assert( p->pSat->qtail == p->pSat->qhead );
    }

    // solve under assumptions
    // A = 1; B = 0     OR     A = 1; B = 1 
    Lit = toLitCond( Cec_ObjSatNum(p,pObjR), Gia_IsComplement(pObj) );
    if ( p->pPars->fPolarFlip )
    {
        // flop by default
        if ( pObjR->fPhase )  Lit = lit_neg( Lit );
    }
    if(testing) printf("    ManSatCheckNode Lit %d\n", Lit);
//Sat_SolverWriteDimacs( p->pSat, "temp.cnf", pLits, pLits + 2, 1 );
// Sat_SolverWriteDimacs( p->pSat, "temp.cnf", &Lit, &Lit + 2, 1 );
clk = Abc_Clock();
    nConflicts = p->pSat->stats.conflicts;

clk2 = Abc_Clock();
    RetValue = sat_solver_solve( p->pSat, &Lit, &Lit + 1, 
        (ABC_INT64_T)nBTLimit, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
//ABC_PRT( "sat", Abc_Clock() - clk2 );

    if ( RetValue == l_False )
    {
p->timeSatUnsat += Abc_Clock() - clk;
        Lit = lit_neg( Lit );
        if(testing) printf("    assumption failed Lit: %d\n", Lit);
        // p->pSat->fPrintClause = 1;
        // assign the literal by adding a clause whose size is 1
        RetValue = sat_solver_addclause( p->pSat, &Lit, &Lit + 1 );
        // p->pSat->fPrintClause = 0;
        assert( RetValue );
        p->nSatUnsat++;
        p->nConfUnsat += p->pSat->stats.conflicts - nConflicts;       
//Abc_Print( 1, "UNSAT after %d conflicts\n", p->pSat->stats.conflicts - nConflicts );
        return 1;
    }
    else if ( RetValue == l_True )
    {
p->timeSatSat += Abc_Clock() - clk;
        p->nSatSat++;
        p->nConfSat += p->pSat->stats.conflicts - nConflicts;
//Abc_Print( 1, "SAT after %d conflicts\n", p->pSat->stats.conflicts - nConflicts );
        return 0;
    }
    else // if ( RetValue == l_Undef )
    {
p->timeSatUndec += Abc_Clock() - clk;
        p->nSatUndec++;
        p->nConfUndec += p->pSat->stats.conflicts - nConflicts;
//Abc_Print( 1, "UNDEC after %d conflicts\n", p->pSat->stats.conflicts - nConflicts );
        return -1;
    }
}

/**Function*************************************************************

  Synopsis    [Runs equivalence test for the two nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManSatCheckNodeTwo( Cec_ManSat_t * p, Gia_Obj_t * pObj1, Gia_Obj_t * pObj2 )
{
    Gia_Obj_t * pObjR1 = Gia_Regular(pObj1);
    Gia_Obj_t * pObjR2 = Gia_Regular(pObj2);
    int nBTLimit = p->pPars->nBTLimit;
    int Lits[2], RetValue, status, nConflicts;
    abctime clk, clk2;

    if ( pObj1 == Gia_ManConst0(p->pAig) || pObj2 == Gia_ManConst0(p->pAig) || pObj1 == Gia_Not(pObj2) )
        return 1;
    if ( pObj1 == Gia_ManConst1(p->pAig) && (pObj2 == NULL || pObj2 == Gia_ManConst1(p->pAig)) )
    {
        assert( 0 );
        return 0;
    }

    p->nCallsSince++;  // experiment with this!!!
    p->nSatTotal++;
    
    // check if SAT solver needs recycling
    if ( p->pSat == NULL || 
        (p->pPars->nSatVarMax && 
         p->nSatVars > p->pPars->nSatVarMax && 
         p->nCallsSince > p->pPars->nCallsRecycle) )
        Cec_ManSatSolverRecycle( p );

    // if the nodes do not have SAT variables, allocate them
clk2 = Abc_Clock();
    Cec_CnfNodeAddToSolver( p, pObjR1 );
    Cec_CnfNodeAddToSolver( p, pObjR2 );
//ABC_PRT( "cnf", Abc_Clock() - clk2 );
//Abc_Print( 1, "%d \n", p->pSat->size );

clk2 = Abc_Clock();
//    Cec_SetActivityFactors( p, pObjR1 ); 
//    Cec_SetActivityFactors( p, pObjR2 ); 
//ABC_PRT( "act", Abc_Clock() - clk2 );

    // propage unit clauses
    if ( p->pSat->qtail != p->pSat->qhead )
    {
        status = sat_solver_simplify(p->pSat);
        assert( status != 0 );
        assert( p->pSat->qtail == p->pSat->qhead );
    }

    // solve under assumptions
    // A = 1; B = 0     OR     A = 1; B = 1 
    Lits[0] = toLitCond( Cec_ObjSatNum(p,pObjR1), Gia_IsComplement(pObj1) );
    Lits[1] = toLitCond( Cec_ObjSatNum(p,pObjR2), Gia_IsComplement(pObj2) );
    if ( p->pPars->fPolarFlip )
    {
        if ( pObjR1->fPhase )  Lits[0] = lit_neg( Lits[0] );
        if ( pObjR2->fPhase )  Lits[1] = lit_neg( Lits[1] );
    }
//Sat_SolverWriteDimacs( p->pSat, "temp.cnf", pLits, pLits + 2, 1 );
clk = Abc_Clock();
    nConflicts = p->pSat->stats.conflicts;

clk2 = Abc_Clock();
    RetValue = sat_solver_solve( p->pSat, Lits, Lits + 2, 
        (ABC_INT64_T)nBTLimit, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
//ABC_PRT( "sat", Abc_Clock() - clk2 );

    if ( RetValue == l_False )
    {
p->timeSatUnsat += Abc_Clock() - clk;
        Lits[0] = lit_neg( Lits[0] );
        Lits[1] = lit_neg( Lits[1] );
        RetValue = sat_solver_addclause( p->pSat, Lits, Lits + 2 );
        assert( RetValue );
        p->nSatUnsat++;
        p->nConfUnsat += p->pSat->stats.conflicts - nConflicts;       
//Abc_Print( 1, "UNSAT after %d conflicts\n", p->pSat->stats.conflicts - nConflicts );
        return 1;
    }
    else if ( RetValue == l_True )
    {
p->timeSatSat += Abc_Clock() - clk;
        p->nSatSat++;
        p->nConfSat += p->pSat->stats.conflicts - nConflicts;
//Abc_Print( 1, "SAT after %d conflicts\n", p->pSat->stats.conflicts - nConflicts );
        return 0;
    }
    else // if ( RetValue == l_Undef )
    {
p->timeSatUndec += Abc_Clock() - clk;
        p->nSatUndec++;
        p->nConfUndec += p->pSat->stats.conflicts - nConflicts;
//Abc_Print( 1, "UNDEC after %d conflicts\n", p->pSat->stats.conflicts - nConflicts );
        return -1;
    }
}


/**Function*************************************************************

  Synopsis    [Performs one round of solving for the POs of the AIG.]

  Description [Labels the nodes that have been proved (pObj->fMark1) 
  and returns the set of satisfying assignments.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Cex_t * Cex_ManGenSimple( Cec_ManSat_t * p, int iOut )
{
    Abc_Cex_t * pCex;
    pCex = Abc_CexAlloc( 0, Gia_ManCiNum(p->pAig), 1 );
    pCex->iPo = iOut;
    pCex->iFrame = 0;
    return pCex;
}
Abc_Cex_t * Cex_ManGenCex( Cec_ManSat_t * p, int iOut )
{
    Abc_Cex_t * pCex;
    int i;
    pCex = Abc_CexAlloc( 0, Gia_ManCiNum(p->pAig), 1 );
    pCex->iPo = iOut;
    pCex->iFrame = 0;
    for ( i = 0; i < Gia_ManCiNum(p->pAig); i++ )
    {
        int iVar = Cec_ObjSatNum(p, Gia_ManCi(p->pAig, i));
        if ( iVar > 0 && sat_solver_var_value(p->pSat, iVar) )
            pCex->pData[i>>5] |= (1<<(i & 31));     
    }
    return pCex;
}
void Cec_ManSatSolve( Cec_ManPat_t * pPat, Gia_Man_t * pAig, Cec_ParSat_t * pPars, Vec_Int_t * vIdsOrig, Vec_Int_t * vMiterPairs, Vec_Int_t * vEquivPairs, int f0Proved )
{
    lbool testing = false;
    Bar_Progress_t * pProgress = NULL;
    Cec_ManSat_t * p;
    Gia_Obj_t * pObj;
    int i, status;
    abctime clk = Abc_Clock(), clk2;
    Vec_PtrFreeP( &pAig->vSeqModelVec );
    if ( pPars->fSaveCexes )
        pAig->vSeqModelVec = Vec_PtrStart( Gia_ManCoNum(pAig) );
    // reset the manager
    if ( pPat )
    {
        pPat->iStart = Vec_StrSize(pPat->vStorage);
        pPat->nPats = 0;
        pPat->nPatLits = 0;
        pPat->nPatLitsMin = 0;
    } 
    Gia_ManSetPhase( pAig );
    Gia_ManLevelNum( pAig );
    Gia_ManIncrementTravId( pAig );
    p = Cec_ManSatCreate( pAig, pPars );
    pProgress = Bar_ProgressStart( stdout, Gia_ManPoNum(pAig) );
    if(testing) printf("size of pAig->vCos: %d \n", Vec_IntSize(pAig->vCos));
    Gia_ManForEachCo( pAig, pObj, i )
    // i.e. for ( i = 0; (i < Vec_IntSize(pAig->vCos)) && ((pObj) = Gia_ManCo(pAig, i)); i++ )
    {
        // for testing
        // printf("ManSatSolve pObj %d\n", Gia_ObjId(pAig, pObj));
        if ( Gia_ObjIsConst0(Gia_ObjFanin0(pObj)) )
        {
            status = !Gia_ObjFaninC0(pObj);
            pObj->fMark0 = (status == 0);
            pObj->fMark1 = (status == 1);
            if ( pPars->fSaveCexes )
                Vec_PtrWriteEntry( pAig->vSeqModelVec, i, status ? (Abc_Cex_t *)(ABC_PTRINT_T)1 : Cex_ManGenSimple(p, i) );
            if(testing) printf("should jump to next co in Cec_ManSatSolve\n");
            continue;
        }
        Bar_ProgressUpdate( pProgress, i, "SAT..." );
clk2 = Abc_Clock();
        // printf("ManSatSolve Gia_ObjChild0(pObj) %d\n", Gia_ObjId(pAig, Gia_ObjChild0(pObj)));
        // if(testing) printf("ManSatSolve pObj %d  Gia_ObjChild0(pObj) %d\n", Gia_ObjId(pAig, pObj), Gia_ObjId(pAig, Gia_ObjChild0(pObj)));

        // Cec_ManTFIPrint(pAig, pObj);

        if(testing) printf("ManSatSolve pObj %d  Gia_ObjChild0(pObj) %d Gia_ObjChild1(pObj) %d\n", Gia_ObjId(pAig, pObj), 
            Gia_ObjId(pAig, Gia_ObjChild0(pObj)), Gia_ObjId(pAig, Gia_ObjChild1(pObj)));
        // printf("obj is co?? %s\n", Gia_ObjIsCo(pObj)?"yes":"no");   // yes
        // printf("obj is and?? %s\n", Gia_ObjChild0(pObj) ?"yes":"no");   // yes
        // return 1 for unsat; 0 for sat; -1 for undef
        status = Cec_ManSatCheckNode( p, Gia_ObjChild0(pObj) );
        if(testing) printf("sat status %d (%s)\n\n", status, status==1?"unsat":(status==0?"sat":"undef"));
        pObj->fMark0 = (status == 0);   // sat, disproved
        pObj->fMark1 = (status == 1);   // unsat, proved
        // if(status==1) printf("unsat ");
        // if(vIdsOrig) printf("vIdsOrig ");
        // if(pPars->fSaveCexes) printf("fSaveCexes ");
        // if(status==1 || pPars->fSaveCexes || vIdsOrig)  printf("|\n");
        if ( status == 1 && vIdsOrig )
        {
            int iObj1 = Vec_IntEntry(vMiterPairs, 2*i);
            int iObj2 = Vec_IntEntry(vMiterPairs, 2*i+1);
            int OrigId1 = Vec_IntEntry(vIdsOrig, iObj1);
            int OrigId2 = Vec_IntEntry(vIdsOrig, iObj2);
            assert( OrigId1 >= 0 && OrigId2 >= 0 );
            Vec_IntPushTwo( vEquivPairs, OrigId1, OrigId2 );
            // printf("pushing %d and %d into vEquivPairs\n", OrigId1, OrigId2);
        }
        if ( pPars->fSaveCexes && status != -1 )
            Vec_PtrWriteEntry( pAig->vSeqModelVec, i, status ? (Abc_Cex_t *)(ABC_PTRINT_T)1 : Cex_ManGenCex(p, i) );

        if ( f0Proved && status == 1 )
            Gia_ManPatchCoDriver( pAig, i, 0 );

        if ( status != 0 )
            continue;
        // save the pattern
        if ( pPat )
        {
            abctime clk3 = Abc_Clock();
            if(testing) printf("save pattern\n");
            // if(! ((Gia_ObjFanin0(pObj)->fMark1 ^ Gia_ObjFaninC0(pObj)) == 1))
            //     printf("assert1: %d %d %d\n", Gia_ObjFanin0(pObj)->fMark1, Gia_ObjFaninC0(pObj), (Gia_ObjFanin0(pObj)->fMark1 ^ Gia_ObjFaninC0(pObj)));
            // assert( (Gia_ObjFanin0(pObj)->fMark1 ^ Gia_ObjFaninC0(pObj)) == 1 );
            Cec_ManPatSavePattern( pPat, p, pObj );
            pPat->timeTotalSave += Abc_Clock() - clk3;
        }
        // quit if one of them is solved
        if ( pPars->fCheckMiter )
            break;
    }
    p->timeTotal = Abc_Clock() - clk;
    Bar_ProgressStop( pProgress );
    if ( pPars->fVerbose )
        Cec_ManSatPrintStats( p );
    Cec_ManSatStop( p );
}

void Cec_ManSatSolve_Dual( Cec_ManPat_t * pPat, Gia_Man_t * pAig, Cec_ParSat_t * pPars, Vec_Int_t * vIdsOrig, Vec_Int_t * vMiterPairs, Vec_Int_t * vEquivPairs, int f0Proved )
{
    // for testing **
    if ( pPars->fVerbose)
        Abc_Print( 1, "Enter cecSolve.c/Cec_ManSatSolve_Dual()\n" );

    Bar_Progress_t * pProgress = NULL;
    // Cec_ManSat_t * p1, *p2;
    Gia_Obj_t * pObj;
    int i, status;
    abctime clk = Abc_Clock(), clk2;
    Vec_PtrFreeP( &pAig->vSeqModelVec );
    if ( pPars->fSaveCexes )
        pAig->vSeqModelVec = Vec_PtrStart( Gia_ManCoNum(pAig) );
    // reset the manager
    if ( pPat )
    {
        pPat->iStart = Vec_StrSize(pPat->vStorage);
        pPat->nPats = 0;
        pPat->nPatLits = 0;
        pPat->nPatLitsMin = 0;
    } 
    Gia_ManSetPhase( pAig );
    Gia_ManLevelNum( pAig );
    Gia_ManIncrementTravId( pAig );
    Cec_ManSat_t * p1 = Cec_ManSatCreate( pAig, pPars );
    Cec_ManSat_t * p2 = Cec_ManSatCreate( pAig, pPars );
    pProgress = Bar_ProgressStart( stdout, Gia_ManPoNum(pAig) );
    // Gia_ManForEachCo( pAig, pObj, i )
    for ( i = 0; (i < Vec_IntSize(pAig->vCos)) && ((pObj) = Gia_ManCo(pAig, i)); i++ )
    {
        Cec_ManSat_t * p;
        if(i%2) p = p1;
        // else continue;
        else p = p2;
        if ( Gia_ObjIsConst0(Gia_ObjFanin0(pObj)) )
        {
            status = !Gia_ObjFaninC0(pObj);
            pObj->fMark0 = (status == 0);
            pObj->fMark1 = (status == 1);
            if ( pPars->fSaveCexes )
                Vec_PtrWriteEntry( pAig->vSeqModelVec, i, status ? (Abc_Cex_t *)(ABC_PTRINT_T)1 : Cex_ManGenSimple(p, i) );
            continue;
        }
        Bar_ProgressUpdate( pProgress, i, "SAT..." );
clk2 = Abc_Clock();
        // return 1 for unsat; 0 for unsat; -1 for undef
        status = Cec_ManSatCheckNode( p, Gia_ObjChild0(pObj) );
        pObj->fMark0 = (status == 0);
        pObj->fMark1 = (status == 1);
        if ( status == 1 && vIdsOrig )
        {
            int iObj1 = Vec_IntEntry(vMiterPairs, 2*i);
            int iObj2 = Vec_IntEntry(vMiterPairs, 2*i+1);
            int OrigId1 = Vec_IntEntry(vIdsOrig, iObj1);
            int OrigId2 = Vec_IntEntry(vIdsOrig, iObj2);
            assert( OrigId1 >= 0 && OrigId2 >= 0 );
            Vec_IntPushTwo( vEquivPairs, OrigId1, OrigId2 );
        }
        if ( pPars->fSaveCexes && status != -1 )
            Vec_PtrWriteEntry( pAig->vSeqModelVec, i, status ? (Abc_Cex_t *)(ABC_PTRINT_T)1 : Cex_ManGenCex(p, i) );

        if ( f0Proved && status == 1 )
            Gia_ManPatchCoDriver( pAig, i, 0 );

        if ( status != 0 )
            continue;
        // save the pattern
        if ( pPat )
        {
            abctime clk3 = Abc_Clock();
            Cec_ManPatSavePattern( pPat, p, pObj );
            pPat->timeTotalSave += Abc_Clock() - clk3;
        }
        // quit if one of them is solved
        if ( pPars->fCheckMiter )
            break;
    }
    p1->timeTotal = Abc_Clock() - clk;
    p2->timeTotal = Abc_Clock() - clk;
    Bar_ProgressStop( pProgress );
    if ( pPars->fVerbose ){
        Cec_ManSatPrintStats( p1 );
        Cec_ManSatPrintStats( p2 );
    }
    Cec_ManSatStop( p1 );
    Cec_ManSatStop( p2 );
}


#define PAR_THR_MAX 20
typedef struct Par_ThData_t_
{
    Cec_ManSat_t * p;
    Gia_Obj_t * pObj;
    Cec_ManPat_t *pPat;
    Gia_Man_t * pAig;
    Cec_ParSat_t * pPars;
    Vec_Int_t * vIdsOrig;
    Vec_Int_t * vMiterPairs;
    Vec_Int_t * vEquivPairs;
    int f0Proved;
    int iThread;
    int fWorking;
    int pId;
} Par_ThData_t;
pthread_mutex_t mutex;

void *Cec_ManSatSolve_OnePthread(void * pArg ){
    // pthread_mutex_lock(&mutex);
    Par_ThData_t * pThData = (Par_ThData_t *)pArg;
    Cec_ManSat_t * p = pThData->p;
    Gia_Obj_t * pObj = pThData->pObj;
    Cec_ManPat_t *pPat = pThData->pPat;
    Gia_Man_t * pAig = pThData->pAig;
    Cec_ParSat_t * pPars = pThData->pPars;
    Vec_Int_t * vIdsOrig = pThData->vIdsOrig;
    Vec_Int_t * vMiterPairs = pThData->vMiterPairs;
    Vec_Int_t * vEquivPairs = pThData->vEquivPairs;
    int f0Proved =  pThData->f0Proved;
    int i = pThData->pId;
    int iThread = pThData->iThread;
    abctime clk = Abc_Clock(), clk2;
    Bar_Progress_t * pProgress = NULL;
    int status;
    lbool testing = false;
    if(testing) printf("    in thread %d\n", iThread);
    // printf("    in thread %d on obj %d %d\n", iThread, i, pThData->fWorking);
    // Gia_ManForEachCo( pAig, pObj, i )
    // for ( i = 0; (i < Vec_IntSize(pAig->vCos)) && ((pObj) = Gia_ManCo(pAig, i)); i++ )
    // {
    if ( Gia_ObjIsConst0(Gia_ObjFanin0(pObj)) )
    {
        status = !Gia_ObjFaninC0(pObj);
        // printf("before %d %d\n", pObj->fMark0, pObj->fMark1);
        pObj->fMark0 = (status == 0);
        pObj->fMark1 = (status == 1);
        if ( pPars->fSaveCexes )
            Vec_PtrWriteEntry( pAig->vSeqModelVec, i, status ? (Abc_Cex_t *)(ABC_PTRINT_T)1 : Cex_ManGenSimple(p, i) );
        // continue;
        goto finalize;
    }
    Bar_ProgressUpdate( pProgress, i, "SAT..." );
clk2 = Abc_Clock();
    // return 1 for unsat; 0 for sat; -1 for undef
    // printf(">>> Cec_CnfNodeAddToSolver %.1f %.1f \n",   (double)p->pSat->stats.clauses, (double)p->pSat->stats.clauses_literals);
    status = Cec_ManSatCheckNode( p, Gia_ObjChild0(pObj) );
    pObj->fMark0 = (status == 0);
    pObj->fMark1 = (status == 1);
    if ( status == 1 && vIdsOrig )
    {
        int iObj1 = Vec_IntEntry(vMiterPairs, 2*i);
        int iObj2 = Vec_IntEntry(vMiterPairs, 2*i+1);
        int OrigId1 = Vec_IntEntry(vIdsOrig, iObj1);
        int OrigId2 = Vec_IntEntry(vIdsOrig, iObj2);
        assert( OrigId1 >= 0 && OrigId2 >= 0 );
        Vec_IntPushTwo( vEquivPairs, OrigId1, OrigId2 );
    }
    if ( pPars->fSaveCexes && status != -1 )
        Vec_PtrWriteEntry( pAig->vSeqModelVec, i, status ? (Abc_Cex_t *)(ABC_PTRINT_T)1 : Cex_ManGenCex(p, i) );

    if ( f0Proved && status == 1 )
        Gia_ManPatchCoDriver( pAig, i, 0 );

    if ( status != 0 ){
        goto finalize;
    }
    // save the pattern
    if ( pPat)
    {
        if(testing ) printf("    thread %d need lock\n", iThread);
        assert( pthread_mutex_lock(&mutex)==0 );
        // pthread_mutex_lock(&mutex);
        if(testing ) printf("    thread %d using lock\n", iThread);

// printf("\ncheck whether thread %d is really sat\n", iThread);
// printf("child0 %c%d\n", Gia_ObjFaninC0(pObj)?'!':' ', Gia_ObjId(p->pAig, Gia_ObjFanin0(pObj)));
// int value0 = Cec_ManPatPrintTFICNF(p, p->pAig, Gia_ObjFanin0(pObj));
// if(!(value0^Gia_ObjFaninC0(pObj))){
//     printf("assert failed at fanin0 %d, thread %d\n", Gia_ObjId(p->pAig, Gia_ObjFanin0(pObj)), iThread);
//     exit(0);
// }
// assert( (value0^Gia_ObjFaninC0(pObj)) ==1);

        abctime clk3 = Abc_Clock();
        // if(! ((Gia_ObjFanin0(pObj)->fMark1 ^ Gia_ObjFaninC0(pObj)) == 1))
        //     printf("assert1: %d %d %d\n", Gia_ObjFanin0(pObj)->fMark1, Gia_ObjFaninC0(pObj), (Gia_ObjFanin0(pObj)->fMark1 ^ Gia_ObjFaninC0(pObj)));
        // assert( (Gia_ObjFanin0(pObj)->fMark1 ^ Gia_ObjFaninC0(pObj)) == 1 );
        // Cec_ManPatSavePattern( pPat, p, pObj );
        Cec_ManPatSavePattern_Pthread( pPat, p, pObj, iThread);
        pPat->timeTotalSave += Abc_Clock() - clk3;
        if(testing ) printf("    thread %d free lock\n", iThread);
// sleep(1);
        assert( pthread_mutex_unlock(&mutex)==0 );
        // pthread_mutex_unlock(&mutex);
    }
    // quit if one of them is solved
    if ( pPars->fCheckMiter ){
        goto finalize;
    }
    // }
finalize:

    // printf("    done thread %d\n", iThread);
    // printf("    done1 thread %d %d %d\n", iThread, i, pThData->fWorking);
    p->timeTotal = Abc_Clock() - clk;
    Bar_ProgressStop( pProgress );
    Cec_ManSatStop( p );
    if(testing) printf("    done thread %d on obj %d %d\n", iThread, i, pThData->fWorking);
    // pthread_mutex_unlock(&mutex);
    pThData->fWorking = 0;
    pthread_exit( NULL );
    assert(0);
    // return NULL;
}


void Cec_ManSatSolve_Pthread( Cec_ManPat_t * pPat, Gia_Man_t * pAig, Cec_ParSat_t * pPars, Vec_Int_t * vIdsOrig, Vec_Int_t * vMiterPairs, Vec_Int_t * vEquivPairs, int f0Proved )
{
    int nProcs = pPars->fMultiThread;
    assert(nProcs>1);
    assert(nProcs<=PAR_THR_MAX);
    // for testing **
    lbool testing = false;
    if ( pPars->fVerbose || testing || true)
        Abc_Print( 1, "Enter cecSolve.c/Cec_ManSatSolve_Pthread()  #thread=%d(%d)\n", nProcs, PAR_THR_MAX );
    if(pPat && testing) printf("save the pattern!!!!!!!!\n");
    else if(testing) printf("don't save pattern\n");
    Bar_Progress_t * pProgress = NULL;
    // Cec_ManSat_t * p1, *p2;
    // Gia_Obj_t * pObj;
    int i,j, status;
    // abctime clk = Abc_Clock(), clk2;
    Vec_PtrFreeP( &pAig->vSeqModelVec );
    if ( pPars->fSaveCexes )
        pAig->vSeqModelVec = Vec_PtrStart( Gia_ManCoNum(pAig) );
    // reset the manager
    if ( pPat )
    {
        pPat->iStart = Vec_StrSize(pPat->vStorage);
        pPat->nPats = 0;
        pPat->nPatLits = 0;
        pPat->nPatLitsMin = 0;
    } 
    Gia_ManSetPhase( pAig );
    Gia_ManLevelNum( pAig );
    Gia_ManIncrementTravId( pAig );

    assert( pthread_mutex_init(&mutex, NULL)==0 );
    // mutex = PTHREAD_MUTEX_INITIALIZER;

    Par_ThData_t ThData[PAR_THR_MAX];
    pthread_t WorkerThread[PAR_THR_MAX];
    for ( i = 0; i < nProcs; i++ ){
        // ThData[i].p = Cec_ManSatCreate( pAig, pPars );
        ThData[i].pPat = pPat;
        ThData[i].pAig = pAig;
        ThData[i].pPars = pPars;
        ThData[i].vIdsOrig = vIdsOrig;
        ThData[i].vMiterPairs = vMiterPairs;
        ThData[i].vEquivPairs = vEquivPairs;
        ThData[i].f0Proved = f0Proved;
        ThData[i].fWorking = 0;
    }

    if(testing) printf("total j: %d\n", Vec_IntSize(pAig->vCos));
    for ( j = 0, i=0; (j < Vec_IntSize(pAig->vCos)); j++, i++ ){
        Gia_Obj_t * pObj = Gia_ManCo(pAig, j);
        i %= nProcs;
        // pthread_join ( WorkerThread[i], NULL );
        // while(ThData[i].fWorking){
        //     printf("    thread %d still working j=%d\n", i, j);
        // }
        // for ( i = 0; i < nProcs; i++ )
        // {
        while ( true ){
            if(ThData[i].fWorking==0)
                break;
            // else printf("   node %d thread %d still working\n", j, i);
            i++;
            i %= nProcs;
        }
        if(testing) printf("j=%d, i=%d\n", j,i);
        // TODO: use it incrementally
        ThData[i].p = Cec_ManSatCreate( pAig, pPars );
        // printf("created %p\n", ThData[i].p);
        ThData[i].pObj = pObj;
        // ThData[i].pPat = pPat;
        // ThData[i].pAig = pAig;
        // ThData[i].pPars = pPars;
        // ThData[i].vIdsOrig = vIdsOrig;
        // ThData[i].vMiterPairs = vMiterPairs;
        // ThData[i].vEquivPairs = vEquivPairs;
        // ThData[i].f0Proved = f0Proved;
        ThData[i].fWorking = 1;
        ThData[i].iThread = i;
        ThData[i].pId = j;

        status = pthread_create( &WorkerThread[i], NULL, Cec_ManSatSolve_OnePthread, (void *)(ThData + i) );
        // }

        // the code below is not working
        // if(i==nProcs-1){
        //     for (int k = 0; k < nProcs; k++)
        //         pthread_join(WorkerThread[k], NULL);
        // }
    }

    pProgress = Bar_ProgressStart( stdout, Gia_ManPoNum(pAig) );

    Bar_ProgressStop( pProgress );
    // if ( pPars->fVerbose ){
    //     Cec_ManSatPrintStats( p1 );
    //     Cec_ManSatPrintStats( p2 );
    // }
    // pthread_mutex_destroy(&mutex);
    // assert( pthread_mutex_destroy(&mutex)==0 );
    if(testing) printf("all done safely!!!\n");
    // pthread_exit(NULL);

    // for (int k = 0; k < nProcs; k++){
        // printf("waiting for thread %d\n", k);
        // if(ThData[k].fWorking)
        // pthread_join(WorkerThread[k], NULL);
        // printf("done for thread %d\n", k);
    // }
    // wait for all used threads to finish
    for ( int k = 0; k < nProcs; k++ )
        if ( ThData[k].fWorking )
            k = -1;
    assert( pthread_mutex_destroy(&mutex)==0 );
    if(testing) printf("all done safely!!!\n");
    // sleep(1);
    return;
}


/**Function*************************************************************

  Synopsis    [Performs one round of solving for the POs of the AIG.]

  Description [Labels the nodes that have been proved (pObj->fMark1) 
  and returns the set of satisfying assignments.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManSatSolveExractPattern( Vec_Int_t * vCexStore, int iStart, Vec_Int_t * vPat )
{
    int k, nSize;
    Vec_IntClear( vPat );
    // skip the output number
    iStart++;
    // get the number of items
    nSize = Vec_IntEntry( vCexStore, iStart++ );
    if ( nSize <= 0 )
        return iStart;
    // extract pattern
    for ( k = 0; k < nSize; k++ )
        Vec_IntPush( vPat, Vec_IntEntry( vCexStore, iStart++ ) );
    return iStart;
}
void Cec_ManSatSolveCSat( Cec_ManPat_t * pPat, Gia_Man_t * pAig, Cec_ParSat_t * pPars )
{
    Vec_Str_t * vStatus;
    Vec_Int_t * vPat = Vec_IntAlloc( 1000 );
    Vec_Int_t * vCexStore = Cbs_ManSolveMiterNc( pAig, pPars->nBTLimit, &vStatus, 0, 0 );
    Gia_Obj_t * pObj;
    int i, status, iStart = 0;
    assert( Vec_StrSize(vStatus) == Gia_ManCoNum(pAig) );
    // reset the manager
    if ( pPat )
    {
        pPat->iStart = Vec_StrSize(pPat->vStorage);
        pPat->nPats = 0;
        pPat->nPatLits = 0;
        pPat->nPatLitsMin = 0;
    } 
    Gia_ManForEachCo( pAig, pObj, i )
    {
        status = (int)Vec_StrEntry(vStatus, i);
        pObj->fMark0 = (status == 0);
        pObj->fMark1 = (status == 1);
        if ( Vec_IntSize(vCexStore) > 0 && status != 1 )
            iStart = Cec_ManSatSolveExractPattern( vCexStore, iStart, vPat );
        if ( status != 0 )
            continue;
        // save the pattern
        if ( pPat && Vec_IntSize(vPat) > 0 )
        {
            abctime clk3 = Abc_Clock();
            Cec_ManPatSavePatternCSat( pPat, vPat );
            pPat->timeTotalSave += Abc_Clock() - clk3;
        }
        // quit if one of them is solved
        if ( pPars->fCheckMiter )
            break;
    }
    assert( iStart == Vec_IntSize(vCexStore) );
    Vec_IntFree( vPat );
    Vec_StrFree( vStatus );
    Vec_IntFree( vCexStore );
}



/**Function*************************************************************

  Synopsis    [Returns the pattern stored.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Cec_ManSatReadCex( Cec_ManSat_t * pSat )
{
    return pSat->vCex;
}

/**Function*************************************************************

  Synopsis    [Save values in the cone of influence.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManSatSolveSeq_rec( Cec_ManSat_t * pSat, Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Ptr_t * vInfo, int iPat, int nRegs )
{
    if ( Gia_ObjIsTravIdCurrent(p, pObj) )
        return;
    Gia_ObjSetTravIdCurrent(p, pObj);
    if ( Gia_ObjIsCi(pObj) )
    {
        unsigned * pInfo = (unsigned *)Vec_PtrEntry( vInfo, nRegs + Gia_ObjCioId(pObj) );
        if ( Cec_ObjSatVarValue( pSat, pObj ) != Abc_InfoHasBit( pInfo, iPat ) )
            Abc_InfoXorBit( pInfo, iPat );
        pSat->nCexLits++;
//        Vec_IntPush( pSat->vCex, Abc_Var2Lit( Gia_ObjCioId(pObj), !Cec_ObjSatVarValue(pSat, pObj) ) );
        return;
    }
    assert( Gia_ObjIsAnd(pObj) );
    Cec_ManSatSolveSeq_rec( pSat, p, Gia_ObjFanin0(pObj), vInfo, iPat, nRegs );
    Cec_ManSatSolveSeq_rec( pSat, p, Gia_ObjFanin1(pObj), vInfo, iPat, nRegs );
}

/**Function*************************************************************

  Synopsis    [Performs one round of solving for the POs of the AIG.]

  Description [Labels the nodes that have been proved (pObj->fMark1) 
  and returns the set of satisfying assignments.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Str_t * Cec_ManSatSolveSeq( Vec_Ptr_t * vPatts, Gia_Man_t * pAig, Cec_ParSat_t * pPars, int nRegs, int * pnPats )
{
    Bar_Progress_t * pProgress = NULL;
    Vec_Str_t * vStatus;
    Cec_ManSat_t * p;
    Gia_Obj_t * pObj;
    int iPat = 0, nPatsInit, nPats;
    int i, status;
    abctime clk = Abc_Clock();
    nPatsInit = nPats = 32 * Vec_PtrReadWordsSimInfo(vPatts);
    Gia_ManSetPhase( pAig );
    Gia_ManLevelNum( pAig );
    Gia_ManIncrementTravId( pAig );
    p = Cec_ManSatCreate( pAig, pPars );
    vStatus = Vec_StrAlloc( Gia_ManPoNum(pAig) );
    pProgress = Bar_ProgressStart( stdout, Gia_ManPoNum(pAig) );
    Gia_ManForEachCo( pAig, pObj, i )
    {
        Bar_ProgressUpdate( pProgress, i, "SAT..." );
        if ( Gia_ObjIsConst0(Gia_ObjFanin0(pObj)) )
        {
            if ( Gia_ObjFaninC0(pObj) )
            {
//                Abc_Print( 1, "Constant 1 output of SRM!!!\n" );
                Vec_StrPush( vStatus, 0 );
            }
            else
            {
//                Abc_Print( 1, "Constant 0 output of SRM!!!\n" );
                Vec_StrPush( vStatus, 1 );
            }
            continue;
        }
        status = Cec_ManSatCheckNode( p, Gia_ObjChild0(pObj) );
//Abc_Print( 1, "output %d   status = %d\n", i, status );
        Vec_StrPush( vStatus, (char)status );
        if ( status != 0 )
            continue;
        // resize storage
        if ( iPat == nPats )
        {
            int nWords = Vec_PtrReadWordsSimInfo(vPatts);
            Vec_PtrReallocSimInfo( vPatts );
            Vec_PtrCleanSimInfo( vPatts, nWords, 2*nWords );
            nPats = 32 * Vec_PtrReadWordsSimInfo(vPatts);
        }
        if ( iPat % nPatsInit == 0 )
            iPat++;
        // save the pattern
        Gia_ManIncrementTravId( pAig );
//        Vec_IntClear( p->vCex );
        Cec_ManSatSolveSeq_rec( p, pAig, Gia_ObjFanin0(pObj), vPatts, iPat++, nRegs );
//        Gia_SatVerifyPattern( pAig, pObj, p->vCex, p->vVisits );
//        Cec_ManSatAddToStore( p->vCexStore, p->vCex );
//        if ( iPat == nPats )
//            break;
        // quit if one of them is solved
//        if ( pPars->fFirstStop )
//            break;
//        if ( iPat == 32 * 15 * 16 - 1 )
//            break;
    }
    p->timeTotal = Abc_Clock() - clk;
    Bar_ProgressStop( pProgress );
    if ( pPars->fVerbose )
        Cec_ManSatPrintStats( p );
//    Abc_Print( 1, "Total number of cex literals = %d. (Ave = %d)\n", p->nCexLits, p->nCexLits/p->nSatSat );
    Cec_ManSatStop( p );
    if ( pnPats )
        *pnPats = iPat-1;
    return vStatus;
}


/**Function*************************************************************

  Synopsis    [Save values in the cone of influence.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManSatAddToStore( Vec_Int_t * vCexStore, Vec_Int_t * vCex, int Out )
{
    int i, Entry;
    Vec_IntPush( vCexStore, Out );
    if ( vCex == NULL ) // timeout
    {
        Vec_IntPush( vCexStore, -1 );
        return;
    }
    // write the counter-example
    Vec_IntPush( vCexStore, Vec_IntSize(vCex) );
    Vec_IntForEachEntry( vCex, Entry, i )
        Vec_IntPush( vCexStore, Entry );
}

/**Function*************************************************************

  Synopsis    [Save values in the cone of influence.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManSatSolveMiter_rec( Cec_ManSat_t * pSat, Gia_Man_t * p, Gia_Obj_t * pObj )
{
    if ( Gia_ObjIsTravIdCurrent(p, pObj) )
        return;
    Gia_ObjSetTravIdCurrent(p, pObj);
    if ( Gia_ObjIsCi(pObj) )
    {
        pSat->nCexLits++;
        Vec_IntPush( pSat->vCex, Abc_Var2Lit( Gia_ObjCioId(pObj), !Cec_ObjSatVarValue(pSat, pObj) ) );
        return;
    }
    assert( Gia_ObjIsAnd(pObj) );
    Cec_ManSatSolveMiter_rec( pSat, p, Gia_ObjFanin0(pObj) );
    Cec_ManSatSolveMiter_rec( pSat, p, Gia_ObjFanin1(pObj) );
}

/**Function*************************************************************

  Synopsis    [Save patterns.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManSavePattern( Cec_ManSat_t * p, Gia_Obj_t * pObj1, Gia_Obj_t * pObj2 )
{
    Vec_IntClear( p->vCex );
    Gia_ManIncrementTravId( p->pAig );
    Cec_ManSatSolveMiter_rec( p, p->pAig, Gia_Regular(pObj1) );
    if ( pObj2 )
    Cec_ManSatSolveMiter_rec( p, p->pAig, Gia_Regular(pObj2) );
}

/**Function*************************************************************

  Synopsis    [Performs one round of solving for the POs of the AIG.]

  Description [Labels the nodes that have been proved (pObj->fMark1) 
  and returns the set of satisfying assignments.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Cec_ManSatSolveMiter( Gia_Man_t * pAig, Cec_ParSat_t * pPars, Vec_Str_t ** pvStatus )
{
    Bar_Progress_t * pProgress = NULL;
    Vec_Int_t * vCexStore;
    Vec_Str_t * vStatus;
    Cec_ManSat_t * p;
    Gia_Obj_t * pObj;
    int i, status;
    abctime clk = Abc_Clock();
    // prepare AIG
    Gia_ManSetPhase( pAig );
    Gia_ManLevelNum( pAig );
    Gia_ManIncrementTravId( pAig );
    // create resulting data-structures
    vStatus = Vec_StrAlloc( Gia_ManPoNum(pAig) );
    vCexStore = Vec_IntAlloc( 10000 );
    // perform solving
    p = Cec_ManSatCreate( pAig, pPars );
    pProgress = Bar_ProgressStart( stdout, Gia_ManPoNum(pAig) );
    Gia_ManForEachCo( pAig, pObj, i )
    {
        Vec_IntClear( p->vCex );
        Bar_ProgressUpdate( pProgress, i, "SAT..." );
        if ( Gia_ObjIsConst0(Gia_ObjFanin0(pObj)) )
        {
            if ( Gia_ObjFaninC0(pObj) )
            {
//                Abc_Print( 1, "Constant 1 output of SRM!!!\n" );
                Cec_ManSatAddToStore( vCexStore, p->vCex, i ); // trivial counter-example
                Vec_StrPush( vStatus, 0 );
            }
            else
            {
//                Abc_Print( 1, "Constant 0 output of SRM!!!\n" );
                Vec_StrPush( vStatus, 1 );
            }
            continue;
        }
        status = Cec_ManSatCheckNode( p, Gia_ObjChild0(pObj) );
        Vec_StrPush( vStatus, (char)status );
        if ( status == -1 )
        {
            Cec_ManSatAddToStore( vCexStore, NULL, i ); // timeout
            continue;
        }
        if ( status == 1 )
            continue;
        assert( status == 0 );
        // save the pattern
//        Gia_ManIncrementTravId( pAig );
//        Cec_ManSatSolveMiter_rec( p, pAig, Gia_ObjFanin0(pObj) );
        Cec_ManSavePattern( p, Gia_ObjFanin0(pObj), NULL );
//        Gia_SatVerifyPattern( pAig, pObj, p->vCex, p->vVisits );
        Cec_ManSatAddToStore( vCexStore, p->vCex, i );
    }
    p->timeTotal = Abc_Clock() - clk;
    Bar_ProgressStop( pProgress );
//    if ( pPars->fVerbose )
//        Cec_ManSatPrintStats( p );
    Cec_ManSatStop( p );
    *pvStatus = vStatus;
    return vCexStore;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

