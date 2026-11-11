/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.Functoriality
public import Nyll.EtaleFundamentalGroups.GeometricFiber.PointedCover
public import Nyll.EtaleFundamentalGroups.GaloisCategories.GaloisObjectQuotient
public import Nyll.EtaleFundamentalGroups.GaloisCategories.FiberIso

/-!
# Intertwining points supplied by actual reconstructed covers

An actual cover map over the fixed reconstructed base induces a point of
its actual pullback. Transport through the fixed base fiber comparison
then gives a point intertwining every original source group element with
its prescribed target deck transformation. No intertwining point or orbit
condition is an assumption. The same construction is valid for a morphism
of covers; an isomorphism is not required.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- An actual commuting and deck-compatible square supplies the finite
Galois-fiber pointing needed for full-inner reconstruction. The point is
constructed using the scheme-theoretic pullback and the fixed base pointing;
no geometric-orbit assertion is made. -/
theorem exists_intertwiningPoint_of_scheme_deck_square
    {S T : Scheme.{u}} [ConnectedSpace S] [ConnectedSpace T]
    {ΩS ΩT : Type u} [Field ΩS] [Field ΩT] [IsSepClosed ΩS] [IsSepClosed ΩT]
    (s : Spec (.of ΩS) ⟶ S) (t : Spec (.of ΩT) ⟶ T)
    (I : S ⟶ T) (tI : pullback I ⋙ fiber s ≅ fiber t)
    (e : π₁ᵉᵗ(s) → π₁ᵉᵗ(t))
    (A : FiniteEtale S) (B : FiniteEtale T) [IsGalois A] [IsGalois B]
    (a : (fiber s).obj A) (b : (fiber t).obj B)
    (f : A.left ⟶ B.left) (hsquare : A.hom ≫ I = f ≫ B.hom)
    (hdeck : ∀ g : π₁ᵉᵗ(s),
      (galoisObjectQuotientMonoidHom (fiber s) π₁ᵉᵗ(s) A a g).unop.asIso.hom.left ≫ f =
        f ≫ (galoisObjectQuotientMonoidHom (fiber t) π₁ᵉᵗ(t) B b (e g)).unop.asIso.hom.left) :
    ∃ y : (fiber t).obj B, ∀ g : π₁ᵉᵗ(s),
      autHomOfCompIso (pullback I) tI g • y = (fiber t).map
        ((galoisObjectQuotientMonoidHom (fiber t) π₁ᵉᵗ(t) B b (e g)).unop.asIso.hom) y := by
  let fA : A.left ⟶ S := A.hom
  let fB : B.left ⟶ T := B.hom
  let h : A ⟶ (pullback I).obj B := MorphismProperty.Over.homMk
    (Limits.pullback.lift f fA hsquare.symm) (Limits.pullback.lift_snd _ _ _)
  refine ⟨tI.hom.app B ((fiber s).map h a), ?_⟩
  intro g
  let σA := (galoisObjectQuotientMonoidHom (fiber s) π₁ᵉᵗ(s) A a g).unop
  let σB := (galoisObjectQuotientMonoidHom (fiber t) π₁ᵉᵗ(t) B b (e g)).unop
  have hh : σA.asIso.hom ≫ h = h ≫ (pullback I).map σB.asIso.hom := by
    let dA : A.left ⟶ A.left := σA.asIso.hom.left
    let dB : B.left ⟶ B.left := σB.asIso.hom.left
    let dP : Limits.pullback fB I ⟶ Limits.pullback fB I :=
      ((pullback I).map σB.asIso.hom).left
    have hfst : dP ≫ Limits.pullback.fst fB I = Limits.pullback.fst fB I ≫ dB :=
      Limits.pullback.lift_fst _ _ _
    have hsnd : dP ≫ Limits.pullback.snd fB I = Limits.pullback.snd fB I :=
      Limits.pullback.lift_snd _ _ _
    apply MorphismProperty.Over.Hom.ext
    apply Limits.pullback.hom_ext
    · change (dA ≫ Limits.pullback.lift f fA hsquare.symm) ≫
          Limits.pullback.fst fB I =
        (Limits.pullback.lift f fA hsquare.symm ≫ dP) ≫ Limits.pullback.fst fB I
      rw [Category.assoc, Limits.pullback.lift_fst, Category.assoc,
        hfst, ← Category.assoc, Limits.pullback.lift_fst]
      exact hdeck g
    · change (dA ≫ Limits.pullback.lift f fA hsquare.symm) ≫
          Limits.pullback.snd fB I =
        (Limits.pullback.lift f fA hsquare.symm ≫ dP) ≫ Limits.pullback.snd fB I
      rw [Category.assoc, Limits.pullback.lift_snd, Category.assoc,
        hsnd, Limits.pullback.lift_snd]
      exact MorphismProperty.Over.w σA.asIso.hom
  have haction (z : (fiber s).obj ((pullback I).obj B)) :
      autHomOfCompIso (pullback I) tI g • tI.hom.app B z =
        tI.hom.app B (g • z) := by
    change tI.hom.app B (g.asIso.hom.app ((pullback I).obj B)
      (tI.inv.app B (tI.hom.app B z))) = tI.hom.app B (g • z)
    have hz : tI.inv.app B (tI.hom.app B z) = z :=
      ConcreteCategory.congr_hom (tI.hom_inv_id_app B) z
    exact congrArg (fun w => tI.hom.app B (g.asIso.hom.app ((pullback I).obj B) w)) hz
  calc
    autHomOfCompIso (pullback I) tI g • tI.hom.app B ((fiber s).map h a) =
        tI.hom.app B (g • (fiber s).map h a) := haction _
    _ = tI.hom.app B ((fiber s).map h (g • a)) :=
      congrArg (tI.hom.app B) (mulAction_naturality (fiber s) g h a)
    _ = tI.hom.app B ((fiber s).map h ((fiber s).map σA.asIso.hom a)) :=
      congrArg (fun z => tI.hom.app B ((fiber s).map h z))
        (galoisObjectQuotientMonoidHom_evaluation (fiber s) π₁ᵉᵗ(s) A a g).symm
    _ = tI.hom.app B ((fiber s).map ((pullback I).map σB.asIso.hom)
        ((fiber s).map h a)) := by
      change tI.hom.app B (((fiber s).map σA.asIso.hom ≫ (fiber s).map h) a) =
        tI.hom.app B (((fiber s).map h ≫ (fiber s).map ((pullback I).map σB.asIso.hom)) a)
      rw [← Functor.map_comp, ← Functor.map_comp, hh]
    _ = (fiber t).map σB.asIso.hom (tI.hom.app B ((fiber s).map h a)) :=
      ConcreteCategory.congr_hom (tI.hom.naturality σB.asIso.hom) ((fiber s).map h a)

/-- Native cover deck squares give actual finite-level pointings at any
fixed original base points. Fiber comparison transports the literal deck
quotients themselves, so the original full group map is retained. -/
theorem exists_intertwiningPoint_of_native_scheme_deck_square
    {S T : Scheme.{u}} [ConnectedSpace S] [ConnectedSpace T]
    {ΩS ΩT ΩA ΩB : Type u} [Field ΩS] [Field ΩT] [Field ΩA] [Field ΩB]
    [IsSepClosed ΩS] [IsSepClosed ΩT] [IsSepClosed ΩA] [IsSepClosed ΩB]
    (s : Spec (.of ΩS) ⟶ S) (t : Spec (.of ΩT) ⟶ T)
    (A : FiniteEtale S) (B : FiniteEtale T) [IsGalois A] [IsGalois B]
    (x : Spec (.of ΩA) ⟶ A.left) (y : Spec (.of ΩB) ⟶ B.left)
    (sA : fiber (x ≫ (show A.left ⟶ S from A.hom)) ≅ fiber s)
    (sB : fiber (y ≫ (show B.left ⟶ T from B.hom)) ≅ fiber t)
    (e : π₁ᵉᵗ(s) ≃ₜ* π₁ᵉᵗ(t))
    (I : S ⟶ T) (tI : pullback I ⋙ fiber s ≅ fiber t)
    (f : A.left ⟶ B.left) (hsquare : A.hom ≫ I = f ≫ B.hom)
    (hdeck : ∀ g : π₁ᵉᵗ(x ≫ (show A.left ⟶ S from A.hom)),
      (galoisObjectQuotientMonoidHom (fiber (x ≫ (show A.left ⟶ S from A.hom)))
        π₁ᵉᵗ(x ≫ (show A.left ⟶ S from A.hom))
        A (liftedFiberPoint A x) g).unop.asIso.hom.left ≫ f =
      f ≫ (galoisObjectQuotientMonoidHom (fiber (y ≫ (show B.left ⟶ T from B.hom)))
        π₁ᵉᵗ(y ≫ (show B.left ⟶ T from B.hom))
        B (liftedFiberPoint B y)
        (((continuousConjAut sA).trans
          (e.trans (continuousConjAut sB).symm)) g)).unop.asIso.hom.left) :
    ∃ z : (fiber t).obj B, ∀ g : π₁ᵉᵗ(s),
      autHomOfCompIso (pullback I) tI g • z = (fiber t).map
        ((galoisObjectQuotientMonoidHom (fiber t) π₁ᵉᵗ(t) B
          (sB.hom.app B (liftedFiberPoint B y)) (e g)).unop.asIso.hom) z := by
  apply exists_intertwiningPoint_of_scheme_deck_square s t I tI e A B
    (sA.hom.app A (liftedFiberPoint A x)) (sB.hom.app B (liftedFiberPoint B y)) f hsquare
  intro g
  let gA := (continuousConjAut sA).symm g
  let gB := (continuousConjAut sB).symm (e g)
  have hA := galoisObjectQuotientMonoidHom_fiberIso
    (fiber (x ≫ (show A.left ⟶ S from A.hom))) (fiber s) sA A (liftedFiberPoint A x) gA
  have hB := galoisObjectQuotientMonoidHom_fiberIso
    (fiber (y ≫ (show B.left ⟶ T from B.hom))) (fiber t) sB B (liftedFiberPoint B y) gB
  change galoisObjectQuotientMonoidHom (fiber s) π₁ᵉᵗ(s) A
    (sA.hom.app A (liftedFiberPoint A x)) ((continuousConjAut sA) gA) = _ at hA
  change galoisObjectQuotientMonoidHom (fiber t) π₁ᵉᵗ(t) B
    (sB.hom.app B (liftedFiberPoint B y)) ((continuousConjAut sB) gB) = _ at hB
  dsimp only [gA] at hA
  dsimp only [gB] at hB
  rw [ContinuousMulEquiv.apply_symm_apply] at hA hB
  rw [hA, hB]
  have h := hdeck gA
  simpa only [ContinuousMulEquiv.trans_apply, ContinuousMulEquiv.apply_symm_apply, gA] using h

end AlgebraicGeometry.FiniteEtale
