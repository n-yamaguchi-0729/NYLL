/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.Basic
public import Nyll.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.CyclotomicQuotient
public import Nyll.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.Decomposition
public import Nyll.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.DenseTorsion
public import Nyll.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.FiniteFree
public import Nyll.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.FiniteOrder
public import Nyll.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.FreeCoordinate
public import Nyll.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.Gather
public import Nyll.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.Local
public import Nyll.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.Swap
public import Nyll.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.TorsionQuotientEquiv
public import Nyll.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.TorsionQuotientMk

/-!
# Cyclotomic decomposition of the profinite unit group

The compiled child modules combine the local decompositions of all
`ℤ_[p]ˣ` into a splitting of `ℤ̂ˣ` with one torsion-free
profinite-integer factor and a product of finite groups.
-/
