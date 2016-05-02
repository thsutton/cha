-- |

module Extract where

import Derivation
import Term

extract :: Derivation -> Term
extract deriv =
    case deriv of
        PI_EQ{} -> TT
        LAM_EQ{} -> TT
        AP_EQ{} -> TT
        FUN_EXT{} -> TT
        PAIR_EQ{} -> TT
        FST_EQ{} -> TT
        SND_EQ{} -> TT
        NAT_EQ{} -> TT
        SIG_EQ{} -> TT
        ZERO_EQ -> TT
        SUCC_EQ{} -> TT
        NATREC_EQ{} -> TT
        UNIT_EQ -> TT
        TT_EQ -> TT
        EQ_EQ{} -> TT
        EQ_MEM_EQ{} -> TT
        EQ_SYM{} -> TT
        CEQ_EQ{} -> TT
        CEQ_MEM_EQ{} -> TT
        CEQ_SYM{} -> TT
        CEQ_STEP{} -> TT
        CEQ_REFL -> TT
        BASE_EQ -> TT
        BASE_MEM_EQ{} -> TT
        PER_EQ{} -> TT
        PER_MEM_EQ{} -> TT
        UNI_EQ -> TT
        VAR_EQ -> TT

        CEQ_SUBST _ _ d -> extract d
        EQ_SUBST _ _ _ _ d -> extract d
        PI_INTRO _ _ d -> Lam (extract d)
        PI_ELIM fIdx arg _ d -> subst (Ap (Var fIdx) arg) 0 (extract d)
        SIG_INTRO _ t _ d _ -> Pair t (extract d)
        SIG_ELIM sigIdx d ->
          subst (Snd (Var sigIdx)) 0
                (subst (Fst (Var (sigIdx + 1))) 0 (extract d))
        NAT_INTRO -> Zero
        NAT_ELIM i d1 d2 ->
          NatRec (Var i)
              (subst TT 0 (extract d1))
              -- This is designed to remove the binding for the equality
              -- hypothesis in d2 just like we did for d1
              (subst TT 0 (extract d2))
        UNIT_INTRO -> TT
        BASE_ELIM_EQ i d -> subst TT 0 (extract d)
        -- Justified by hidden hyp
        PER_ELIM_EQ i d -> subst TT 0 (extract d)
        CUMULATIVE _ -> TT
        WITNESS t _ -> t
        VAR i -> Var i
#ifdef FLAG_coind
        -- TODO Cases for co/inductive types.
#endif
