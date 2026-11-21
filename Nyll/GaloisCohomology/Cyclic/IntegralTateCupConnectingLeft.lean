/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex), Claude

The two dimension-shifting arguments follow
`TauCeti/RepresentationTheory/Homological/TateCohomology/Cup/Delta.lean`
at commit ca32605ff53921fa0689dd312618b7cfaafa7e43.
-/

module

public import Nyll.GaloisCohomology.Cyclic.IntegralTateCupConnecting
public import Nyll.GaloisCohomology.Cyclic.IntegralTateThreeByThree

/-!
# The first-variable Tate cup rule for split coefficient sequences

The two tensor boundaries anticommute. In an upward or downward shift of
the second variable this sign cancels the change in the degree of the
first variable under its connecting map.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory
open scoped RepTensor

namespace IntegralGroupCohomology.Universe

variable {G : Type u} [Group G] [Fintype G]

/-- The diagram whose rows are left tensors of `T` and whose columns are
right tensors of `S`. -/
private def tensorDiagram (S T : ShortComplex (Rep.{u} ℤ G)) :
    ShortComplex (ShortComplex (Rep.{u} ℤ G)) :=
  ShortComplex.mk (T.mapNatTrans (Rep.diagonalTensorLeftNatTrans S.f))
    (T.mapNatTrans (Rep.diagonalTensorLeftNatTrans S.g)) (by
      apply ShortComplex.hom_ext
      all_goals
        change (Rep.diagonalTensorRight _).map S.f ≫ (Rep.diagonalTensorRight _).map S.g = 0
        rw [← Functor.map_comp, S.zero, Functor.map_zero])

/-- The signed equality of the two composites in the actual tensor diagram. -/
private theorem tensorBoundary_anticommute {S T : ShortComplex (Rep.{u} ℤ G)}
    (s : (S.map (forget₂ (Rep.{u} ℤ G) (ModuleCat.{u} ℤ))).Splitting)
    (t : (T.map (forget₂ (Rep.{u} ℤ G) (ModuleCat.{u} ℤ))).Splitting) (n : ℤ)
    (c : tate (S.X₃ ⊗ᵣ T.X₃) n) :
    tateδ (Rep.tensorRight_shortExact_of_forget_splitting T.X₁ s) (n + 1)
        (tateδ (Rep.tensorLeft_shortExact_of_forget_splitting S.X₃ t) n c) =
      -tateδ (Rep.tensorLeft_shortExact_of_forget_splitting S.X₁ t) (n + 1)
        (tateδ (Rep.tensorRight_shortExact_of_forget_splitting T.X₃ s) n c) := by
  have key := tateδ_comp_δ_eq_neg (tensorDiagram S T)
    (Rep.tensorLeft_shortExact_of_forget_splitting S.X₁ t)
    (Rep.tensorLeft_shortExact_of_forget_splitting S.X₂ t)
    (Rep.tensorLeft_shortExact_of_forget_splitting S.X₃ t)
    (Rep.tensorRight_shortExact_of_forget_splitting T.X₁ s)
    (Rep.tensorRight_shortExact_of_forget_splitting T.X₂ s)
    (Rep.tensorRight_shortExact_of_forget_splitting T.X₃ s) n
  exact ConcreteCategory.congr_hom key c

private theorem boundary_smul_units {S : ShortComplex (Rep.{u} ℤ G)}
    (hS : S.ShortExact) (n : ℤ) (a : ℤˣ) (c : tate S.X₃ n) :
    tateδ hS n (a • c) = a • tateδ hS n c := by
  simp only [Units.smul_def]
  exact (tateδ hS n).hom.toAddMonoidHom.map_zsmul (a : ℤ) c

private theorem boundarySign_succ {V : Type*} [AddCommGroup V] [Module ℤ V]
    (p : ℤ) (x : V) : p.negOnePow • (-x) = (p + 1).negOnePow • x := by
  change (p.negOnePow : ℤ) • (-x) = ((p + 1).negOnePow : ℤ) • x
  rw [Int.negOnePow_succ]
  change (p.negOnePow : ℤ) • (-x) = -(p.negOnePow : ℤ) • x
  exact (zsmul_neg x (p.negOnePow : ℤ)).trans (neg_zsmul x (p.negOnePow : ℤ)).symm

/-- The left boundary of a right shift is the signed right boundary of the
left boundary. The sign comes from the tensor diagram's anticommutation. -/
private theorem cupBoundaryLeft_right_shift {S T : ShortComplex (Rep.{u} ℤ G)}
    (hT : T.ShortExact) (s : (S.map (forget₂ (Rep.{u} ℤ G) (ModuleCat.{u} ℤ))).Splitting)
    (t : (T.map (forget₂ (Rep.{u} ℤ G) (ModuleCat.{u} ℤ))).Splitting)
    {p q r : ℤ} (h : p + q = r) (x : tate S.X₃ p) (y : tate T.X₃ q) :
    tateδ (Rep.tensorRight_shortExact_of_forget_splitting T.X₁ s) (r + 1)
        (tateCup S.X₃ T.X₁ p (q + 1) (r + 1) (by omega) x (tateδ hT q y)) =
      (p + 1).negOnePow • tateδ (Rep.tensorLeft_shortExact_of_forget_splitting S.X₁ t) (r + 1)
        (tateδ (Rep.tensorRight_shortExact_of_forget_splitting T.X₃ s) r
          (tateCup S.X₃ T.X₃ p q r h x y)) := by
  let hR₃ := Rep.tensorLeft_shortExact_of_forget_splitting S.X₃ t
  let hR₁ := Rep.tensorLeft_shortExact_of_forget_splitting S.X₁ t
  let hC₁ := Rep.tensorRight_shortExact_of_forget_splitting T.X₁ s
  let hC₃ := Rep.tensorRight_shortExact_of_forget_splitting T.X₃ s
  let c := tateCup S.X₃ T.X₃ p q r h x y
  let a := tateδ hR₁ (r + 1) (tateδ hC₃ r c)
  let b := tateδ hR₃ r c
  let V := tate (S.X₁ ⊗ᵣ T.X₁) (r + 1 + 1)
  let sign (z : V) : V := p.negOnePow • z
  have h₁ := congrArg (tateδ hC₁ (r + 1)) (tateCup_connecting_right S.X₃ hT t h x y)
  have h₂ := boundary_smul_units hC₁ (r + 1) p.negOnePow b
  have h₃ := congrArg sign (tensorBoundary_anticommute s t r c)
  exact h₁.trans (h₂.trans (h₃.trans (boundarySign_succ p a)))

/-- The upward step for the first-variable rule. -/
private theorem cupBoundaryLeft_step_up {S : ShortComplex (Rep.{u} ℤ G)}
    (hS : S.ShortExact) (s : (S.map (forget₂ (Rep.{u} ℤ G) (ModuleCat.{u} ℤ))).Splitting)
    (B : Rep.{u} ℤ G) {p q r : ℤ} (h : p + q = r) (x : tate S.X₃ p)
    (ih : ∀ z : tate (Rep.coindShiftUp B) q,
      tateδ (Rep.tensorRight_shortExact_of_forget_splitting (Rep.coindShiftUp B) s) r
          (tateCup S.X₃ (Rep.coindShiftUp B) p q r h x z) =
        tateCup S.X₁ (Rep.coindShiftUp B) (p + 1) q (r + 1) (by omega) (tateδ hS p x) z)
    (y : tate B (q + 1)) :
    tateδ (Rep.tensorRight_shortExact_of_forget_splitting B s) (r + 1)
        (tateCup S.X₃ B p (q + 1) (r + 1) (by omega) x y) =
      tateCup S.X₁ B (p + 1) (q + 1) (r + 1 + 1) (by omega) (tateδ hS p x) y := by
  obtain ⟨z, rfl⟩ := (coindShiftUpEquiv B q).surjective y
  let hT := Rep.coindShiftSequence_shortExact B
  let t := Rep.coindShiftSequence_forget_splitting B
  let d := tateδ (Rep.tensorLeft_shortExact_of_forget_splitting S.X₁ t) (r + 1)
  have h₁ := cupBoundaryLeft_right_shift hT s t h x z
  have h₂ := congrArg (fun a => (p + 1).negOnePow • d a) (ih z)
  have h₃ := tateCup_connecting_right S.X₁ hT t (by omega : (p + 1) + q = r + 1)
    (tateδ hS p x) z
  exact h₁.trans (h₂.trans h₃.symm)

/-- The downward step for the first-variable rule. -/
private theorem cupBoundaryLeft_step_down {S : ShortComplex (Rep.{u} ℤ G)}
    (hS : S.ShortExact) (s : (S.map (forget₂ (Rep.{u} ℤ G) (ModuleCat.{u} ℤ))).Splitting)
    (B : Rep.{u} ℤ G) {p q r : ℤ} (h : p + q = r) (x : tate S.X₃ p)
    (ih : ∀ z : tate (Rep.indShiftDown B) (q + 1),
      tateδ (Rep.tensorRight_shortExact_of_forget_splitting (Rep.indShiftDown B) s) (r + 1)
          (tateCup S.X₃ (Rep.indShiftDown B) p (q + 1) (r + 1) (by omega) x z) =
        tateCup S.X₁ (Rep.indShiftDown B) (p + 1) (q + 1) (r + 1 + 1) (by omega)
          (tateδ hS p x) z)
    (y : tate B q) :
    tateδ (Rep.tensorRight_shortExact_of_forget_splitting B s) r (tateCup S.X₃ B p q r h x y) =
      tateCup S.X₁ B (p + 1) q (r + 1) (by omega) (tateδ hS p x) y := by
  let hT := Rep.indShiftSequence_shortExact B
  let t := Rep.indShiftSequence_forget_splitting B
  let hR := Rep.tensorLeft_shortExact_of_forget_splitting S.X₁ t
  let V := tate (S.X₁ ⊗ᵣ Rep.indShiftDown B) (r + 1 + 1)
  let sign : Equiv.Perm V := MulAction.toPerm (p + 1).negOnePow
  have hinj := tateδ_injective_of_isZero_middle hR (r + 1)
    (tate_tensorIndBot_isZero S.X₁ (Rep.res (⊥ : Subgroup G).subtype B) (r + 1))
  have h₁ := cupBoundaryLeft_right_shift hT s t h x y
  have h₂ := ih (tateδ hT q y)
  have h₃ := tateCup_connecting_right S.X₁ hT t (by omega : (p + 1) + q = r + 1)
    (tateδ hS p x) y
  exact hinj (sign.injective (h₁.symm.trans (h₂.trans h₃)))

/-- In every integer bidegree, the actual connecting map for a sequence split
on the underlying modules commutes with the cup product in its first variable. -/
theorem tateCup_connecting_left (B : Rep.{u} ℤ G) {S : ShortComplex (Rep.{u} ℤ G)}
    (hS : S.ShortExact) (s : (S.map (forget₂ (Rep.{u} ℤ G) (ModuleCat.{u} ℤ))).Splitting)
    {p q r : ℤ} (h : p + q = r) (x : tate S.X₃ p) (y : tate B q) :
    tateCup S.X₁ B (p + 1) q (r + 1) (by omega) (tateδ hS p x) y =
      tateδ (Rep.tensorRight_shortExact_of_forget_splitting B s) r
        (tateCup S.X₃ B p q r h x y) := by
  symm
  have hzero (B : Rep.{u} ℤ G) (r : ℤ) (h : p + 0 = r) (y : tate B 0) :
      tateδ (Rep.tensorRight_shortExact_of_forget_splitting B s) r (tateCup S.X₃ B p 0 r h x y) =
        tateCup S.X₁ B (p + 1) 0 (r + 1) (by omega) (tateδ hS p x) y := by
    have hr : r = p := h.symm.trans (add_zero p)
    revert h
    rw [hr]
    intro h
    have h₃ := congrArg
      (fun f => tateδ (Rep.tensorRight_shortExact_of_forget_splitting B s) p (f x y))
      (tateCup_zero_right S.X₃ B p (add_zero p))
    have h₁ := congrArg (fun f => f (tateδ hS p x) y)
      (tateCup_zero_right S.X₁ B (p + 1) (add_zero (p + 1)))
    exact h₃.trans ((tateCupZeroRight_connecting_left B hS
      (Rep.tensorRight_shortExact_of_forget_splitting B s) p x y).symm.trans h₁.symm)
  have hpos (i : ℕ) : ∀ (B : Rep.{u} ℤ G) (r : ℤ) (h : p + (i : ℤ) = r)
      (y : tate B (i : ℤ)),
      tateδ (Rep.tensorRight_shortExact_of_forget_splitting B s) r
          (tateCup S.X₃ B p i r h x y) =
        tateCup S.X₁ B (p + 1) i (r + 1) (by omega) (tateδ hS p x) y := by
    induction i with
    | zero => exact hzero
    | succ i ih =>
      intro B r h y
      obtain rfl : r = (p + (i : ℤ)) + 1 := by omega
      exact cupBoundaryLeft_step_up hS s B (p := p) (q := (i : ℤ)) (r := p + (i : ℤ))
        rfl x (ih (Rep.coindShiftUp B) (p + (i : ℤ)) rfl) y
  have hneg (i : ℕ) : ∀ (B : Rep.{u} ℤ G) (r : ℤ) (h : p + Int.negSucc i = r)
      (y : tate B (Int.negSucc i)),
      tateδ (Rep.tensorRight_shortExact_of_forget_splitting B s) r
          (tateCup S.X₃ B p (Int.negSucc i) r h x y) =
        tateCup S.X₁ B (p + 1) (Int.negSucc i) (r + 1) (by omega) (tateδ hS p x) y := by
    induction i with
    | zero =>
      intro B r h y
      exact cupBoundaryLeft_step_down hS s B h x (hzero (Rep.indShiftDown B) (r + 1) (by omega)) y
    | succ i ih =>
      intro B r h y
      exact cupBoundaryLeft_step_down hS s B h x (ih (Rep.indShiftDown B) (r + 1) (by omega)) y
  cases q with
  | ofNat i => exact hpos i B r h y
  | negSucc i => exact hneg i B r h y

end IntegralGroupCohomology.Universe
