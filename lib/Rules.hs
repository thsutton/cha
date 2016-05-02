-- |
--
-- This module contains the tactics which treat specifically in the
-- term and derivation languages.
module Rules
    ( module Base
    , module Ceq
    , module Eq
    , module Pi
    , module General
    ) where

import Rules.Base    as Base
import Rules.Ceq     as Ceq
import Rules.Eq      as Eq
import Rules.General as General
import Rules.Pi      as Pi
