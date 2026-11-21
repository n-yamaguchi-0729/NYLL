/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex), The Tau Ceti contributors

Adapted from `TauCeti/RepresentationTheory/Homological/TateCohomology/HomologySequence.lean`
at commit ca32605ff53921fa0689dd312618b7cfaafa7e43.
-/

module

public import Nyll.GaloisCohomology.Cyclic.IntegralTateExactness
public import Nyll.SchemeTheory.HomologicalAlgebra.HomologySequenceThreeByThree

/-!
# The two corner connecting maps in integral Tate cohomology

Applying the actual Tate complex to a diagram of representations transports
the sign rule for connecting maps to the original integral Tate groups.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory

namespace IntegralGroupCohomology.Universe

private def mapDiagram {C C' : Type*} [Category C] [Category C']
    [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms C']
    (F : C ⥤ C') [F.PreservesZeroMorphisms] (D : ShortComplex (ShortComplex C)) :
    ShortComplex (ShortComplex C') := by
  let P := F.mapShortComplex
  let : P.PreservesZeroMorphisms :=
    ⟨fun _ _ => by apply ShortComplex.hom_ext <;> exact F.map_zero _ _⟩
  exact D.map P

private theorem mapDiagram_columns {C C' : Type*} [Category C] [Category C']
    [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms C']
    (F : C ⥤ C') [F.PreservesZeroMorphisms] (D : ShortComplex (ShortComplex C)) :
    let D' := mapDiagram F D
    D'.map ShortComplex.π₁ = (D.map ShortComplex.π₁).map F ∧
      D'.map ShortComplex.π₂ = (D.map ShortComplex.π₂).map F ∧
      D'.map ShortComplex.π₃ = (D.map ShortComplex.π₃).map F :=
  ⟨rfl, rfl, rfl⟩

private theorem mappedBoundaries_anticommute {C A A' I : Type*}
    [Category C] [Limits.HasZeroMorphisms C] [Category A] [Abelian A]
    [Category A'] [Preadditive A'] {c : ComplexShape I}
    (F : C ⥤ HomologicalComplex A c) [F.PreservesZeroMorphisms]
    (J : A ⥤ A') [J.Additive] (D : ShortComplex (ShortComplex C))
    (h₁ : (D.X₁.map F).ShortExact) (h₂ : (D.X₂.map F).ShortExact)
    (h₃ : (D.X₃.map F).ShortExact) (h₁' : ((D.map ShortComplex.π₁).map F).ShortExact)
    (h₂' : ((D.map ShortComplex.π₂).map F).ShortExact)
    (h₃' : ((D.map ShortComplex.π₃).map F).ShortExact)
    (i j k : I) (hij : c.Rel i j) (hjk : c.Rel j k) :
    J.map (h₃.δ i j hij) ≫ J.map (h₁'.δ j k hjk) =
      -(J.map (h₃'.δ i j hij) ≫ J.map (h₁.δ j k hjk)) := by
  let D' := mapDiagram F D
  obtain ⟨hp₁, hp₂, hp₃⟩ := mapDiagram_columns F D
  have hh₁ : D'.X₁.ShortExact := h₁
  have hh₂ : D'.X₂.ShortExact := h₂
  have hh₃ : D'.X₃.ShortExact := h₃
  have hh₁' : (D'.map ShortComplex.π₁).ShortExact := hp₁.symm ▸ h₁'
  have hh₂' : (D'.map ShortComplex.π₂).ShortExact := hp₂.symm ▸ h₂'
  have hh₃' : (D'.map ShortComplex.π₃).ShortExact := hp₃.symm ▸ h₃'
  let W := (F.obj D.X₃.X₃).homology i
  let X := (F.obj D.X₃.X₁).homology j
  let Y := (F.obj D.X₁.X₃).homology j
  let Z := (F.obj D.X₁.X₁).homology k
  let a : W ⟶ X := h₃.δ i j hij
  let b : X ⟶ Z := h₁'.δ j k hjk
  let d : W ⟶ Y := h₃'.δ i j hij
  let e : Y ⟶ Z := h₁.δ j k hjk
  have h : a ≫ b = -(d ≫ e) :=
    HomologicalComplex.HomologySequence.δ_comp_δ_eq_neg D' hh₁ hh₂ hh₃ hh₁' hh₂' hh₃'
      i j k hij hjk
  change J.map a ≫ J.map b = -(J.map d ≫ J.map e)
  calc
    _ = J.map (a ≫ b) := (J.map_comp a b).symm
    _ = J.map (-(d ≫ e)) := congrArg (fun f : W ⟶ Z => J.map f) h
    _ = _ := (J.map_neg (f := d ≫ e)).trans (congrArg Neg.neg (J.map_comp d e))

variable {G : Type u} [Group G] [Fintype G]

private def nativeTateComplex (G : Type u) [Group G] [Fintype G] :
    Rep.{v} ℤ G ⥤ CochainComplex (ModuleCat.{max u v} (ULift.{max u v} ℤ)) ℤ :=
  nativeFunctor.{u, v} G ⋙ tateComplexFunctor (ULift.{max u v} ℤ) (ULift.{v} G)

private instance nativeTateComplex_preservesZero :
    (nativeTateComplex.{u, v} G).PreservesZeroMorphisms := by
  unfold nativeTateComplex
  infer_instance

private theorem nativeTateComplex_shortExact
    (S : ShortComplex (Rep.{v} ℤ G)) (hS : S.ShortExact) :
    (S.map (nativeTateComplex G)).ShortExact := by
  let U := nativeFunctor.{u, v} G
  let T := tateComplexFunctor (ULift.{max u v} ℤ) (ULift.{v} G)
  exact (ShortComplex.map_comp S U T).symm ▸
    TateCohomology.map_tateComplexFunctor_shortExact (native_shortExact hS)

private theorem tateδ_eq_nativeTateComplex_boundary
    (S : ShortComplex (Rep.{v} ℤ G)) (hS : S.ShortExact) (n : ℤ) :
    tateδ hS n = integerScalars.{max u v}.map
      ((nativeTateComplex_shortExact S hS).δ n (n + 1) rfl) := rfl

private theorem nativeMappedBoundaries_anticommute
    (D : ShortComplex (ShortComplex (Rep.{v} ℤ G)))
    (h₁ : D.X₁.ShortExact) (h₂ : D.X₂.ShortExact) (h₃ : D.X₃.ShortExact)
    (h₁' : (D.map ShortComplex.π₁).ShortExact)
    (h₂' : (D.map ShortComplex.π₂).ShortExact)
    (h₃' : (D.map ShortComplex.π₃).ShortExact) (n : ℤ) :
    let J := integerScalars.{max u v}
    let map_exact := nativeTateComplex_shortExact (G := G)
    J.map ((map_exact D.X₃ h₃).δ n (n + 1) rfl) ≫
      J.map ((map_exact (D.map ShortComplex.π₁) h₁').δ (n + 1) (n + 1 + 1) rfl) =
      -(J.map ((map_exact (D.map ShortComplex.π₃) h₃').δ n (n + 1) rfl) ≫
        J.map ((map_exact D.X₁ h₁).δ (n + 1) (n + 1 + 1) rfl)) := by
  intro J map_exact
  exact mappedBoundaries_anticommute (nativeTateComplex.{u, v} G) J D
    (map_exact D.X₁ h₁) (map_exact D.X₂ h₂) (map_exact D.X₃ h₃)
    (map_exact (D.map ShortComplex.π₁) h₁') (map_exact (D.map ShortComplex.π₂) h₂')
    (map_exact (D.map ShortComplex.π₃) h₃') n (n + 1) (n + 1 + 1) rfl rfl

/-- In a `3 × 3` diagram with short exact rows and columns, the two composites
of original integral Tate connecting maps to the opposite corner anticommute. -/
theorem tateδ_comp_δ_eq_neg (D : ShortComplex (ShortComplex (Rep.{v} ℤ G)))
    (h₁ : D.X₁.ShortExact) (h₂ : D.X₂.ShortExact) (h₃ : D.X₃.ShortExact)
    (h₁' : (D.map ShortComplex.π₁).ShortExact)
    (h₂' : (D.map ShortComplex.π₂).ShortExact)
    (h₃' : (D.map ShortComplex.π₃).ShortExact) (n : ℤ) :
    tateδ h₃ n ≫ tateδ h₁' (n + 1) = -(tateδ h₃' n ≫ tateδ h₁ (n + 1)) := by
  let map_exact := nativeTateComplex_shortExact (G := G)
  let J := integerScalars.{max u v}
  let A := tate D.X₃.X₃ n
  let B := tate D.X₃.X₁ (n + 1)
  let C := tate D.X₁.X₃ (n + 1)
  let E := tate D.X₁.X₁ (n + 1 + 1)
  let a : A ⟶ B := J.map ((map_exact D.X₃ h₃).δ n (n + 1) rfl)
  let b : B ⟶ E := J.map ((map_exact (D.map ShortComplex.π₁) h₁').δ
    (n + 1) (n + 1 + 1) rfl)
  let c : A ⟶ C := J.map ((map_exact (D.map ShortComplex.π₃) h₃').δ n (n + 1) rfl)
  let e : C ⟶ E := J.map ((map_exact D.X₁ h₁).δ (n + 1) (n + 1 + 1) rfl)
  let a₀ : A ⟶ B := tateδ h₃ n
  let b₀ : B ⟶ E := tateδ h₁' (n + 1)
  let c₀ : A ⟶ C := tateδ h₃' n
  let e₀ : C ⟶ E := tateδ h₁ (n + 1)
  have ha : a₀ = a := tateδ_eq_nativeTateComplex_boundary D.X₃ h₃ n
  have hb : b₀ = b := tateδ_eq_nativeTateComplex_boundary (D.map ShortComplex.π₁) h₁' (n + 1)
  have hc : c₀ = c := tateδ_eq_nativeTateComplex_boundary (D.map ShortComplex.π₃) h₃' n
  have he : e₀ = e := tateδ_eq_nativeTateComplex_boundary D.X₁ h₁ (n + 1)
  have h : a ≫ b = -(c ≫ e) := nativeMappedBoundaries_anticommute D h₁ h₂ h₃ h₁' h₂' h₃' n
  change a₀ ≫ b₀ = -(c₀ ≫ e₀)
  exact (congrArg₂ (· ≫ ·) ha hb).trans (h.trans (congrArg₂ (fun x y => -(x ≫ y)) hc he).symm)

end IntegralGroupCohomology.Universe
