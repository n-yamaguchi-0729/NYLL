/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.CoefficientEndomorphism
public import Nyll.EtaleCohomology.Classical.Etale
public import Nyll.EtaleCohomology.Classical.ModuleCohomology
public import Nyll.EtaleCohomology.Classical.PullbackCohomology
public import Nyll.EtaleCohomology.Frobenius.ExtensionByZero
public import Nyll.EtaleCohomology.Frobenius.SheafComparison
public import Nyll.EtaleCohomology.Sites.ExtensionByZeroBaseChange
public import Nyll.EtaleCohomology.Sites.PullbackComposition
public import Nyll.SchemeTheory.Morphisms.FrobeniusBaseChange

/-!
# Frobenius on extension-by-zero cohomology after extending constants

For an original open immersion `j : U ⟶ X` over a finite field and an arbitrary
module sheaf `F` on `U`, the Frobenius comparison on `F` induces a coefficient
isomorphism on its actual extension by zero. Pullback composition transports
this isomorphism to the base change of the original Frobenius on `X`. The
existing extension-by-zero base-change isomorphism then gives an endomorphism
of the actual cohomology of `jΩ! FΩ`, natural in the original sheaf `F`.

When `X` is proper this is the cohomology model used for compact supports.
The construction itself needs no properness, constructibility, dimension,
or coefficient finiteness assumption. It uses the base change of the original
q-power Frobenius, not the absolute Frobenius of the scheme over the extended
field. No trace formula or independence of compactification is asserted here.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace EtaleCohomology

variable (k : Type u) [Field k] [Fintype k] {U X : Scheme.{u}}
  [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
  (j : U ⟶ X) [IsOpenImmersion j] (R : Type u) [CommRing R]

/-- The Frobenius coefficient isomorphism on the extension by zero is built
from the original sheaf's Frobenius isomorphism and the cartesian open square. -/
def etaleExtensionByZeroFrobeniusCoefficientIso :
    etaleExtensionByZero j R ⋙ etalePullback (X.finiteFieldFrobenius k) R ≅
      etaleExtensionByZero j R :=
  etaleExtensionByZeroFrobeniusIso k j R ≪≫
    Functor.isoWhiskerRight (etaleFrobeniusPullbackIso k U R)
      (etaleExtensionByZero j R) ≪≫
        Functor.leftUnitor (etaleExtensionByZero j R)

variable (Ω : Type u) [Field Ω] [Algebra k Ω] [Algebra.IsAlgebraic k Ω]

local notation "XΩ" => pullback (X ↘ Spec (CommRingCat.of k))
  (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))
local notation "πX" => pullback.fst (X ↘ Spec (CommRingCat.of k))
  (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))
local notation "πU" => pullback.fst j πX
local notation "jΩ" => pullback.snd j πX
/-- The original inverse image followed by extension by zero after extending
constants. Naming the functor once keeps its affine Kan-extension and
sheafification dictionaries shared by coefficient and cohomology maps. -/
def etaleBaseChangeExtensionByZero :
    Sheaf U.smallEtaleTopology (ModuleCat.{u} R) ⥤
      Sheaf (XΩ).smallEtaleTopology (ModuleCat.{u} R) :=
  etalePullback πU R ⋙ etaleExtensionByZero jΩ R

local notation "JΩ" => etaleBaseChangeExtensionByZero k j R Ω

/-- The actual sheaf `jΩ! FΩ` has a Frobenius coefficient isomorphism induced
by the original `F`, using the specified base-changed scheme Frobenius. -/
def etaleBaseChangeExtensionByZeroFrobeniusCoefficientIso :
    JΩ ⋙ etalePullback (Scheme.constantBaseChangeFrobenius k Ω X) R ≅ JΩ := by
  let J := etaleExtensionByZero j R
  let P := etalePullback πX R
  let L := etalePullback (Scheme.constantBaseChangeFrobenius k Ω X) R
  let Q := etalePullback (X.finiteFieldFrobenius k) R
  let e : P ⋙ L ≅ Q ⋙ P :=
    (etalePullbackCompIso (Scheme.constantBaseChangeFrobenius k Ω X) πX R).symm ≪≫
      eqToIso (congrArg (fun f => etalePullback f R)
        (Scheme.constantBaseChangeFrobenius_fst k Ω X)) ≪≫
          etalePullbackCompIso πX (X.finiteFieldFrobenius k) R
  let a : (J ⋙ P) ⋙ L ≅ J ⋙ P :=
    Functor.associator J P L ≪≫
      Functor.isoWhiskerLeft J e ≪≫
        (Functor.associator J Q P).symm ≪≫
          Functor.isoWhiskerRight
            (etaleExtensionByZeroFrobeniusCoefficientIso k j R) P
  let b : J ⋙ P ≅ JΩ := etaleExtensionByZeroBaseChangeIso j πX R
  exact Functor.isoWhiskerRight b.symm L ≪≫ a ≪≫ b

/-- The base change of the original q-power Frobenius acts on the actual
cohomology of the base-changed extension by zero, with arbitrary original
module-sheaf coefficients. -/
def finiteFieldFrobeniusExtensionByZeroCohomology
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u} R)) (n : ℕ) :
    Module.End R (etaleCohomology XΩ R ((JΩ).obj F) n) :=
  etaleCoefficientCohomologyEndomorphism
    (Scheme.constantBaseChangeFrobenius k Ω X) R ((JΩ).obj F)
    ((etaleBaseChangeExtensionByZeroFrobeniusCoefficientIso k j R Ω).hom.app F) n

/-- A morphism of the original sheaves intertwines Frobenius on their
base-changed extension-by-zero cohomology in every degree. -/
theorem finiteFieldFrobeniusExtensionByZeroCohomology_naturality
    {F G : Sheaf U.smallEtaleTopology (ModuleCat.{u} R)} (φ : F ⟶ G) (n : ℕ)
    (x : etaleCohomology XΩ R ((JΩ).obj F) n) :
    finiteFieldFrobeniusExtensionByZeroCohomology k j R Ω G n
        (Classical.cohomologyMap.{u + 1, u, u, u, u} ((JΩ).map φ) n x) =
      Classical.cohomologyMap.{u + 1, u, u, u, u} ((JΩ).map φ) n
        (finiteFieldFrobeniusExtensionByZeroCohomology k j R Ω F n x) := by
  let L := etalePullback (Scheme.constantBaseChangeFrobenius k Ω X) R
  let A := (JΩ).obj F
  let B := (JΩ).obj G
  let ψ : A ⟶ B := (JΩ).map φ
  let eF : L.obj A ⟶ A :=
    (etaleBaseChangeExtensionByZeroFrobeniusCoefficientIso k j R Ω).hom.app F
  let eG : L.obj B ⟶ B :=
    (etaleBaseChangeExtensionByZeroFrobeniusCoefficientIso k j R Ω).hom.app G
  let y : Sheaf.H.{u} (Classical.forgetCoefficients.{u + 1, u, u, u}.obj
      (L.obj A)) n :=
    etaleCohomologyPullbackMap (Scheme.constantBaseChangeFrobenius k Ω X) R A n x
  have h := etaleCohomologyPullbackMap_naturality
    (Scheme.constantBaseChangeFrobenius k Ω X) R ψ n x
  have he : L.map ψ ≫ eG = eF ≫ ψ :=
    (etaleBaseChangeExtensionByZeroFrobeniusCoefficientIso k j R Ω).hom.naturality φ
  have hy :
      Sheaf.H.map (Classical.forgetCoefficients.{u + 1, u, u, u}.map eG) n
        (Sheaf.H.map (Classical.forgetCoefficients.{u + 1, u, u, u}.map
          (L.map ψ)) n y) =
      Sheaf.H.map (Classical.forgetCoefficients.{u + 1, u, u, u}.map ψ) n
        (Sheaf.H.map (Classical.forgetCoefficients.{u + 1, u, u, u}.map eF) n y) := by
    rw [← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply,
      ← Functor.map_comp, ← Functor.map_comp, he]
  exact (congrArg (fun z : etaleCohomology XΩ R (L.obj B) n =>
    Classical.cohomologyMap.{u + 1, u, u, u, u} eG n z) h).trans hy

/-- Every natural power of the constructed Frobenius remains natural in
the original sheaf, with the same extension-by-zero cohomology map. -/
theorem finiteFieldFrobeniusExtensionByZeroCohomology_pow_naturality
    {F G : Sheaf U.smallEtaleTopology (ModuleCat.{u} R)} (φ : F ⟶ G) (n m : ℕ)
    (x : etaleCohomology XΩ R ((JΩ).obj F) n) :
    ((finiteFieldFrobeniusExtensionByZeroCohomology k j R Ω G n) ^ m)
        (Classical.cohomologyMap.{u + 1, u, u, u, u} ((JΩ).map φ) n x) =
      Classical.cohomologyMap.{u + 1, u, u, u, u} ((JΩ).map φ) n
        (((finiteFieldFrobeniusExtensionByZeroCohomology k j R Ω F n) ^ m) x) := by
  let a : Module.End R (etaleCohomology XΩ R ((JΩ).obj F) n) :=
    finiteFieldFrobeniusExtensionByZeroCohomology k j R Ω F n
  let b : Module.End R (etaleCohomology XΩ R ((JΩ).obj G) n) :=
    finiteFieldFrobeniusExtensionByZeroCohomology k j R Ω G n
  let t : etaleCohomology XΩ R ((JΩ).obj F) n →ₗ[R]
      etaleCohomology XΩ R ((JΩ).obj G) n :=
    Classical.cohomologyMap.{u + 1, u, u, u, u} ((JΩ).map φ) n
  change (b ^ m) (t x) = t ((a ^ m) x)
  have h (y : etaleCohomology XΩ R ((JΩ).obj F) n) : b (t y) = t (a y) :=
    finiteFieldFrobeniusExtensionByZeroCohomology_naturality k j R Ω φ n y
  induction m with
  | zero => rfl
  | succ m hm =>
      have hb : (b ^ (m + 1)) (t x) = b ((b ^ m) (t x)) :=
        congrArg (fun z : Module.End R (etaleCohomology XΩ R ((JΩ).obj G) n) =>
          z (t x)) (pow_succ' b m)
      have ha : (a ^ (m + 1)) x = a ((a ^ m) x) :=
        congrArg (fun z : Module.End R (etaleCohomology XΩ R ((JΩ).obj F) n) =>
          z x) (pow_succ' a m)
      exact hb.trans ((congrArg b hm).trans ((h ((a ^ m) x)).trans
        (congrArg t ha.symm)))

end EtaleCohomology
