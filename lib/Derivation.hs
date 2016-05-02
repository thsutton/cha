module Derivation where

import Term

data Derivation
    = PI_EQ Derivation Derivation -- BINDS
    | PI_INTRO Int Derivation Derivation -- BINDS
    | PI_ELIM Int Term Derivation Derivation -- BINDS
    | LAM_EQ Int Derivation Derivation -- BINDS
    | AP_EQ Int Term Derivation Derivation Derivation
    | FUN_EXT Derivation Derivation Derivation -- BINDS
    | SIG_EQ Derivation Derivation -- BINDS
    | SIG_INTRO Int Term Derivation Derivation Derivation -- BINDS
    | SIG_ELIM Int Derivation -- BINDS
    | PAIR_EQ Int Derivation Derivation Derivation -- BINDS
    | FST_EQ Term Derivation
    | SND_EQ Int Term Derivation Derivation
    | NAT_EQ
    | NAT_INTRO
    | NAT_ELIM Int Derivation Derivation -- BINDS
    | ZERO_EQ
    | SUCC_EQ Derivation
    | NATREC_EQ Derivation Derivation Derivation -- BINDS
    | UNIT_EQ
    | TT_EQ
    | UNIT_INTRO
    | EQ_EQ Derivation Derivation Derivation
    | EQ_MEM_EQ Derivation
    | EQ_SYM Derivation
    | EQ_SUBST Int Term Derivation Derivation Derivation -- BINDS
    | CEQ_EQ Derivation Derivation
    | CEQ_MEM_EQ Derivation
    | CEQ_SYM Derivation
    | CEQ_SUBST Term Derivation Derivation
    | CEQ_STEP Derivation
    | CEQ_REFL
    | BASE_EQ
    | BASE_MEM_EQ Derivation
    | BASE_ELIM_EQ Int Derivation
    | UNI_EQ
    | CUMULATIVE Derivation
    | PER_EQ Derivation Derivation Derivation Derivation Derivation Derivation -- BINDS
    | PER_MEM_EQ Int Derivation Derivation Derivation Derivation
    | PER_ELIM_EQ Int Derivation -- BINDS
    | WITNESS Term Derivation
    -- | CUT
    | VAR Int
    | VAR_EQ
#ifdef FLAG_coind
    -- TODO Derivations of co/inductive types.
#endif
  deriving (Eq, Show)
