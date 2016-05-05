-- |
--
-- This module contains the tactics which treat specifically in the
-- term and derivation languages.
module Rules
    ( module Base
    , module Ceq
    , module Eq
    , module General
    , module Nat
    , module Pi
    , module Sigma
    , module Uni
    , module Unit
    , Utils.PrlTactic
    ) where

import Rules.Base    as Base
import Rules.Ceq     as Ceq
import Rules.Eq      as Eq
import Rules.General as General
import Rules.Nat     as Nat
import Rules.Pi      as Pi
import Rules.Sigma   as Sigma
import Rules.Uni     as Uni
import Rules.Unit    as Unit
import Rules.Utils   as Utils
