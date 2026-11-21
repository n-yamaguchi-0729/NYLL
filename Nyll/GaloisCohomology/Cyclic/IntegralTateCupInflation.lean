/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RepresentationTheory.Coinduced
public import Nyll.GaloisCohomology.Cyclic.IntegralTateCupConnecting
public import Nyll.GaloisCohomology.Cyclic.IntegralTateCupInflationFixed
public import Nyll.GaloisCohomology.GroupTheory.CoinducedShiftNaturality

/-!
# Positive Tate cup products commute with pullback

Pullback of the functions in the coinduced shift and the original coefficient
map give a morphism of shifting short exact sequences. Transporting the cup
formula through those sequences extends the fixed-representative formula to
both positive degrees, including quotient inflation.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped RepTensor

namespace IntegralGroupCohomology.Universe

variable {G H : Type u} [Group G] [Group H]

private def coindMiddleMapAlong {A : Rep.{u} ℤ G} {B : Rep.{u} ℤ H}
    (f : H →* G) (a : Rep.res f A ⟶ B) :
    Rep.res f ((Rep.coindShiftMiddleFunctor (R := ℤ) (G := G)).obj A) ⟶
      (Rep.coindShiftMiddleFunctor (R := ℤ) (G := H)).obj B := by
  let P := Rep.res f ((Rep.coindShiftMiddleFunctor (R := ℤ) (G := G)).obj A)
  let Q := (Rep.coindShiftMiddleFunctor (R := ℤ) (G := H)).obj B
  let : Module ℤ P := P.hV2
  let : Module ℤ Q := Q.hV2
  let m : P →ₗ[ℤ] Q := {
    toFun := fun x => ⟨fun h => a (x.val (f h)), by
      intro b h
      have hb : b = 1 := Subsingleton.elim _ _
      subst b
      change a (x.val (f ((1 : H) * h))) = B.ρ 1 (a (x.val (f h)))
      rw [one_mul, map_one, one_apply_eq_self]⟩
    map_add' := fun x y => Subtype.ext (funext fun h => a.hom.map_add (x.val (f h)) (y.val (f h)))
    map_smul' := fun n x =>
      Subtype.ext (funext fun h => a.hom.toLinearMap.map_smul n (x.val (f h))) }
  refine ConcreteCategory.ofHom (C := Rep.{u} ℤ H) (X := P) (Y := Q)
    ⟨m, fun h => ?_⟩
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext t
  change a (x.val (f t * f h)) = a (x.val (f (t * h)))
  rw [map_mul]

private def coindSequenceMapAlong {A : Rep.{u} ℤ G} {B : Rep.{u} ℤ H}
    (f : H →* G) (a : Rep.res f A ⟶ B) :
    (Rep.coindShiftSequence A).map (Rep.resFunctor f) ⟶ Rep.coindShiftSequence B := by
  let F : Rep.{u} ℤ G ⥤ Rep.{u} ℤ H := Rep.resFunctor f
  let S := (Rep.coindShiftSequence A).map F
  let T := Rep.coindShiftSequence B
  let m : S.X₂ ⟶ T.X₂ := coindMiddleMapAlong f a
  have h₁ : a ≫ T.f = S.f ≫ m := by
    apply Rep.hom_ext
    apply DFunLike.ext
    intro x
    apply Subtype.ext
    funext h
    change B.ρ h (a x) = a (A.ρ (f h) x)
    exact (Rep.hom_comm_apply a h x).symm
  let JV := forget₂ (Rep.{u} ℤ G) (ModuleCat.{u} ℤ)
  let JW := forget₂ (Rep.{u} ℤ H) (ModuleCat.{u} ℤ)
  have hW : (S.map JW).ShortExact := (Rep.coindShiftSequence_shortExact A).map_of_exact JV
  have hS : S.ShortExact := {
    exact := JW.reflects_exact_of_faithful S hW.exact
    mono_f := JW.mono_of_mono_map hW.mono_f
    epi_g := JW.epi_of_epi_map hW.epi_g }
  have hz : S.f ≫ m ≫ T.g = 0 :=
    (Category.assoc S.f m T.g).symm.trans
      ((congrArg (· ≫ T.g) h₁.symm).trans ((Category.assoc a T.f T.g).trans
        ((congrArg (a ≫ ·) T.zero).trans comp_zero)))
  let c := CokernelCofork.IsColimit.desc' hS.gIsCokernel (m ≫ T.g) hz
  exact { τ₁ := a, τ₂ := m, τ₃ := c.val, comm₁₂ := h₁, comm₂₃ := c.property.symm }

private def tensorSequenceMapAlong {A : Rep.{u} ℤ G} {B : Rep.{u} ℤ H}
    {S : ShortComplex (Rep.{u} ℤ G)} {T : ShortComplex (Rep.{u} ℤ H)}
    (f : H →* G) (a : Rep.res f A ⟶ B) (c : S.map (Rep.resFunctor f) ⟶ T) :
    (S.map (Rep.diagonalTensorLeft A)).map (Rep.resFunctor f) ⟶
      T.map (Rep.diagonalTensorLeft B) where
  τ₁ := a ⊗ᵣₘ c.τ₁
  τ₂ := a ⊗ᵣₘ c.τ₂
  τ₃ := a ⊗ᵣₘ c.τ₃
  comm₁₂ := by
    change (a ⊗ᵣₘ c.τ₁) ≫ (𝟙 B ⊗ᵣₘ T.f) =
      (𝟙 (Rep.res f A) ⊗ᵣₘ (Rep.resFunctor f).map S.f) ≫ (a ⊗ᵣₘ c.τ₂)
    rw [Rep.diagonalTensorMap_comp, Rep.diagonalTensorMap_comp, Category.comp_id, Category.id_comp,
      c.comm₁₂]
    rfl
  comm₂₃ := by
    change (a ⊗ᵣₘ c.τ₂) ≫ (𝟙 B ⊗ᵣₘ T.g) =
      (𝟙 (Rep.res f A) ⊗ᵣₘ (Rep.resFunctor f).map S.g) ≫ (a ⊗ᵣₘ c.τ₃)
    rw [Rep.diagonalTensorMap_comp, Rep.diagonalTensorMap_comp, Category.comp_id, Category.id_comp,
      c.comm₂₃]
    rfl

variable [Fintype G] [Fintype H]

private theorem positiveMapAlong_sign {A : Rep.{u} ℤ G} {B : Rep.{u} ℤ H}
    (f : H →* G) (a : Rep.res f A ⟶ B) (n : ℕ) [NeZero n] (p : ℤ) (x : tate A n) :
    tatePositiveMapAlong f a n (p.negOnePow • x) = p.negOnePow • tatePositiveMapAlong f a n x := by
  simp only [Units.smul_def]
  exact (tatePositiveMapAlong f a n).hom.toAddMonoidHom.map_zsmul (p.negOnePow : ℤ) x

private theorem cupPositiveMapAlong_step {A B : Rep.{u} ℤ G} {C D : Rep.{u} ℤ H}
    (f : H →* G) (a : Rep.res f A ⟶ C) (b : Rep.res f B ⟶ D)
    {p q r : ℕ} [NeZero p] [NeZero r] (hr : p + q = r)
    (x : tate A p) (z : tate (Rep.coindShiftUp B) q) (w : tate (Rep.coindShiftUp D) q)
    (hδ : tatePositiveMapAlong f b (q + 1) (coindShiftUpEquiv B q z) = coindShiftUpEquiv D q w)
    (hCup :
      tatePositiveMapAlong f (a ⊗ᵣₘ (coindSequenceMapAlong f b).τ₃) r
          (tateCup A (Rep.coindShiftUp B) p q r (by omega) x z) =
        tateCup C (Rep.coindShiftUp D) p q r (by omega) (tatePositiveMapAlong f a p x) w) :
    tatePositiveMapAlong f (a ⊗ᵣₘ b) (r + 1)
        (tateCup A B p (q + 1 : ℕ) (r + 1 : ℕ) (by omega) x (coindShiftUpEquiv B q z)) =
      tateCup C D p (q + 1 : ℕ) (r + 1 : ℕ) (by omega)
        (tatePositiveMapAlong f a p x)
        (tatePositiveMapAlong f b (q + 1) (coindShiftUpEquiv B q z)) := by
  let hSB := Rep.coindShiftSequence_shortExact B
  let hSD := Rep.coindShiftSequence_shortExact D
  let sB := Rep.coindShiftSequence_forget_splitting B
  let sD := Rep.coindShiftSequence_forget_splitting D
  let hAB := Rep.tensorLeft_shortExact_of_forget_splitting A sB
  let hCD := Rep.tensorLeft_shortExact_of_forget_splitting C sD
  let k := coindSequenceMapAlong f b
  let l := tensorSequenceMapAlong f a k
  have h := tatePositiveMapAlong_δ f hAB hCD l r
  let c := tateCup A (Rep.coindShiftUp B) p q r (by omega) x z
  have h' := congrArg
    (fun m : tate (A ⊗ᵣ Rep.coindShiftUp B) r ⟶ tate (C ⊗ᵣ D) (r + 1 : ℕ) => m c) h
  change tatePositiveMapAlong f (a ⊗ᵣₘ b) (r + 1) (tateδ hAB (r : ℤ) c) =
    tateδ hCD r (tatePositiveMapAlong f (a ⊗ᵣₘ k.τ₃) r c) at h'
  have hA := tateCup_connecting_right A hSB sB (by omega : (p : ℤ) + q = r) x z
  have hC := tateCup_connecting_right C hSD sD (by omega : (p : ℤ) + q = r)
    (tatePositiveMapAlong f a p x) w
  change tateCup A B p (q + 1 : ℕ) (r + 1 : ℕ) (by omega) x (coindShiftUpEquiv B q z) =
    (p : ℤ).negOnePow • tateδ hAB r c at hA
  change tateCup C D p (q + 1 : ℕ) (r + 1 : ℕ) (by omega)
    (tatePositiveMapAlong f a p x) (coindShiftUpEquiv D q w) = _ at hC
  let m : Rep.res f (A ⊗ᵣ B) ⟶ C ⊗ᵣ D := a ⊗ᵣₘ b
  let f₁ := tatePositiveMapAlong f m (r + 1)
  let T := tate (C ⊗ᵣ D) (r + 1 : ℕ)
  let sign (v : T) : T := (p : ℤ).negOnePow • v
  let v := tateCup C (Rep.coindShiftUp D) p q r (by omega)
    (tatePositiveMapAlong f a p x) w
  let cD : tate D (q + 1 : ℕ) → T := tateCup C D p (q + 1 : ℕ) (r + 1 : ℕ)
    (by omega) (tatePositiveMapAlong f a p x)
  have h₁ := congrArg f₁ hA
  have h₂ := positiveMapAlong_sign f m (r + 1) (p : ℤ) (tateδ hAB (r : ℤ) c)
  have h₃ := congrArg sign h'
  have h₄ := congrArg (fun v => sign (tateδ hCD (r : ℤ) v)) hCup
  have h₅ : sign (tateδ hCD (r : ℤ) v) = cD (coindShiftUpEquiv D q w) := hC.symm
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans (congrArg cD hδ.symm)))))

/-- Pullback on the original positive Tate groups commutes with cup products
in every pair of positive degrees. -/
theorem tatePositiveMapAlong_cup_succ {A B : Rep.{u} ℤ G} {C D : Rep.{u} ℤ H}
    (f : H →* G) (a : Rep.res f A ⟶ C) (b : Rep.res f B ⟶ D)
    (p q : ℕ) [NeZero p] (x : tate A p) (y : tate B (q + 1 : ℕ)) :
    tatePositiveMapAlong f (a ⊗ᵣₘ b) (p + q + 1)
        (tateCup A B p (q + 1 : ℕ) (p + q + 1 : ℕ) (by omega) x y) =
      tateCup C D p (q + 1 : ℕ) (p + q + 1 : ℕ) (by omega)
        (tatePositiveMapAlong f a p x) (tatePositiveMapAlong f b (q + 1) y) := by
  induction q generalizing B D with
  | zero =>
    obtain ⟨z, rfl⟩ := (coindShiftUpEquiv B 0).surjective y
    obtain ⟨z₀, rfl⟩ := fixedClass_surjective (Rep.coindShiftUp B) z
    let k := coindSequenceMapAlong f b
    let w₀ : (Rep.coindShiftUp D).ρ.invariants := ⟨k.τ₃ z₀.val, fun h => by
      exact (Rep.hom_comm_apply k.τ₃ h z₀.val).symm.trans
        (congrArg k.τ₃ (z₀.property (f h)))⟩
    have hδ := tatePositiveMapAlong_δ_fixedClass f (Rep.coindShiftSequence_shortExact B)
      (Rep.coindShiftSequence_shortExact D) k z₀
    change tatePositiveMapAlong f b 1 (coindShiftUpEquiv B 0 (fixedClass (Rep.coindShiftUp B) z₀)) =
      coindShiftUpEquiv D 0 (fixedClass (Rep.coindShiftUp D) w₀) at hδ
    apply cupPositiveMapAlong_step f a b (q := 0) (r := p) (Nat.add_zero p) x _ _ hδ
    let h₃ : Rep.res f (Rep.coindShiftUp B) ⟶ Rep.coindShiftUp D := k.τ₃
    let m : Rep.res f (A ⊗ᵣ Rep.coindShiftUp B) ⟶ C ⊗ᵣ Rep.coindShiftUp D :=
      a ⊗ᵣₘ h₃
    have hleft := congrArg (fun g => tatePositiveMapAlong f m p
        (g x (fixedClass (Rep.coindShiftUp B) z₀)))
      (tateCup_zero_right A (Rep.coindShiftUp B) (p : ℤ) (add_zero _))
    have hright := congrArg (fun g => g (tatePositiveMapAlong f a p x)
        (fixedClass (Rep.coindShiftUp D) w₀))
      (tateCup_zero_right C (Rep.coindShiftUp D) (p : ℤ) (add_zero _))
    exact hleft.trans
      ((tatePositiveMapAlong_tensorCupZeroRight_fixedClass f a h₃ p x z₀).trans hright.symm)
  | succ q ih =>
    obtain ⟨z, rfl⟩ := (coindShiftUpEquiv B (q + 1 : ℕ)).surjective y
    let k := coindSequenceMapAlong f b
    let w := tatePositiveMapAlong f k.τ₃ (q + 1) z
    have hδ := congrArg
      (fun m : tate (Rep.coindShiftUp B) (q + 1 : ℕ) ⟶ tate D (q + 1 + 1 : ℕ) => m z)
      (tatePositiveMapAlong_δ f (Rep.coindShiftSequence_shortExact B)
        (Rep.coindShiftSequence_shortExact D) k (q + 1))
    change tatePositiveMapAlong f b (q + 1 + 1) (coindShiftUpEquiv B (q + 1 : ℕ) z) =
      coindShiftUpEquiv D (q + 1 : ℕ) w at hδ
    exact cupPositiveMapAlong_step f a b (q := q + 1) (r := p + q + 1) (by omega) x z w hδ
      (@ih (Rep.coindShiftUp B) (Rep.coindShiftUp D) k.τ₃ z)

/-- Quotient inflation in positive degrees commutes with cup product under
the tensor of the actual invariant-coefficient inclusions. -/
theorem tateInflate_cup_succ (S : Subgroup G) [S.Normal] [Fintype (G ⧸ S)]
    (A B : Rep.{u} ℤ G) (p q : ℕ) [NeZero p]
    (x : tate (A.quotientToInvariants S) p) (y : tate (B.quotientToInvariants S) (q + 1 : ℕ)) :
    let f := QuotientGroup.mk' S
    let a : Rep.res f (A.quotientToInvariants S) ⟶ A :=
      ConcreteCategory.ofHom (A.ρ.quotientToInvariants_lift S)
    let b : Rep.res f (B.quotientToInvariants S) ⟶ B :=
      ConcreteCategory.ofHom (B.ρ.quotientToInvariants_lift S)
    tatePositiveMapAlong f (a ⊗ᵣₘ b) (p + q + 1)
        (tateCup (A.quotientToInvariants S) (B.quotientToInvariants S)
          p (q + 1 : ℕ) (p + q + 1 : ℕ) (by omega) x y) =
      tateCup A B p (q + 1 : ℕ) (p + q + 1 : ℕ) (by omega)
        (tateInflate S A p x) (tateInflate S B (q + 1) y) := by
  intro f a b
  exact tatePositiveMapAlong_cup_succ f a b p q x y

end IntegralGroupCohomology.Universe
