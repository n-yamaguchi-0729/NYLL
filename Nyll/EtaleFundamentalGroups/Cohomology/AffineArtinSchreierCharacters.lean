/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.FundamentalGroup
public import Nyll.EtaleFundamentalGroups.Cohomology.TorsorCharacter
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Topology.Instances.ZMod
public import Mathlib.Tactic.Ring
public import Mathlib.CategoryTheory.Endomorphism

/-!
# Artin–Schreier sections on the original finite étale cover

A trace-one section of a finite abelian cover gives an Artin–Schreier section
for every prime-field character of its deck action. Evaluating that section
on the original geometric fiber recovers the original monodromy displacement.
The construction works in the section ring, without a field hypothesis.

Existence of trace-one sections for every affine torsor and descent of the
invariant section to the base ring are separate steps. In particular, this
file does not yet assert the affine Artin–Schreier classification.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups.Cohomology

/-- Trace-one averaging realizes every prime-field character in a commutative
ring with the specified finite group action. -/
theorem exists_translation_of_trace_one
    {G S : Type*} [Group G] [Fintype G] [CommRing S]
    (p : ℕ) [Fact p.Prime] [CharP S p]
    (act : G → S →+* S)
    (hact : ∀ g h x, act g (act h x) = act (g * h) x)
    (t : S) (ht : ∑ g, act g t = 1)
    (χ : G →* Multiplicative (ZMod p)) :
    ∃ β : S, ∀ g, act g β - β = (ZMod.castHom (dvd_refl p) S) (χ g).toAdd := by
  classical
  let c : G → S := fun g => (ZMod.castHom (dvd_refl p) S) (χ g).toAdd
  have hc (g h : G) : c (g * h) = c g + c h := by
    change (ZMod.castHom (dvd_refl p) S) (χ (g * h)).toAdd = _
    rw [map_mul]
    exact map_add _ _ _
  have hfix (g h : G) : act g (c h) = c h := by
    simp only [c, ZMod.castHom_apply, ZMod.cast_eq_val, map_natCast]
  let B : S := ∑ h, c h * act h t
  have hB (g : G) : act g B = B - c g := by
    have hperm : (∑ h, c (g * h) * act (g * h) t) = B :=
      Fintype.sum_bijective (fun h : G => g * h)
        (Group.mulLeft_bijective g) _ _ (fun _ => rfl)
    have htrace : (∑ h, act (g * h) t) = 1 := by
      rw [Fintype.sum_bijective (fun h : G => g * h)
        (Group.mulLeft_bijective g) _ (fun h => act h t) (fun _ => rfl)]
      exact ht
    calc
      act g B = ∑ h, (c (g * h) - c g) * act (g * h) t := by
        dsimp only [B]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro h _
        rw [map_mul, hfix, hact, hc, add_sub_cancel_left]
      _ = (∑ h, c (g * h) * act (g * h) t) -
          c g * ∑ h, act (g * h) t := by
        simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
      _ = B - c g := by rw [hperm, htrace, mul_one]
  refine ⟨-B, fun g => ?_⟩
  rw [map_neg, hB]
  change -(B - c g) - -B = c g
  ring

universe u

variable {X : Scheme.{u}} (W : FiniteEtale X)
  {G : Type*} [CommGroup G] [Fintype G]
  (ρ : G →* Aut W) (p : ℕ) [Fact p.Prime] [CharP Γ(W.left, ⊤) p]

/-- Trace-one averaging takes place in the actual ring of sections of the
cover. The resulting Artin–Schreier section has the prescribed deck character,
and its Artin–Schreier value is invariant under the original deck action. -/
theorem exists_artinSchreierSection_of_trace_one
    (t : Γ(W.left, ⊤)) (ht : ∑ g, (ρ g).asIso.hom.left.appTop t = 1)
    (χ : G →* Multiplicative (ZMod p)) :
    ∃ β : Γ(W.left, ⊤),
      (∀ g, (ρ g).asIso.hom.left.appTop β - β =
        (ZMod.castHom (dvd_refl p) Γ(W.left, ⊤)) (χ g).toAdd) ∧
      ∀ g, (ρ g).asIso.hom.left.appTop (β ^ p - β) = β ^ p - β := by
  let act : G → Γ(W.left, ⊤) →+* Γ(W.left, ⊤) :=
    fun g => (ρ g).asIso.hom.left.appTop.hom
  have hact (g h : G) (x : Γ(W.left, ⊤)) :
      act g (act h x) = act (g * h) x := by
    have hm : (ρ (g * h)).asIso.hom.left =
        (ρ g).asIso.hom.left ≫ (ρ h).asIso.hom.left :=
      congrArg (fun τ : Aut W => τ.asIso.hom.left)
        ((congrArg ρ (mul_comm g h)).trans (map_mul ρ h g))
    exact ((congrArg (fun f : W.left ⟶ W.left => f.appTop x) hm).trans
      (ConcreteCategory.congr_hom
        (Scheme.Hom.comp_appTop (ρ g).asIso.hom.left (ρ h).asIso.hom.left) x)).symm
  obtain ⟨β, hβ⟩ := exists_translation_of_trace_one p act hact t ht χ
  refine ⟨β, hβ, fun g => ?_⟩
  have htranslate := (sub_eq_iff_eq_add).mp (hβ g)
  have hpow :
      ((ZMod.castHom (dvd_refl p) Γ(W.left, ⊤)) (χ g).toAdd) ^ p =
        (ZMod.castHom (dvd_refl p) Γ(W.left, ⊤)) (χ g).toAdd := by
    rw [← map_pow, ZMod.pow_card]
  change act g (β ^ p - β) = β ^ p - β
  rw [map_sub, map_pow, htranslate, add_pow_char, hpow]
  ring

section Fiber

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (ξ : Spec (.of Ω) ⟶ X)

/-- Evaluation of a section at the original geometric fiber point. -/
def finiteEtaleSectionValue (x : (FiniteEtale.fiber ξ).obj W) :
    Γ(W.left, ⊤) →+* Ω :=
  (Scheme.ΓSpecIso (.of Ω)).hom.hom.comp
    (FiniteEtale.fiberObjEquivHom ξ W x).left.appTop.hom

omit [Fintype G] [CharP Γ(W.left, ⊤) p] in
/-- Evaluation respects the actual deck map, by naturality of the geometric
fiber's identification with field-valued scheme morphisms. -/
theorem finiteEtaleSectionValue_deck
    (g : G) (x : (FiniteEtale.fiber ξ).obj W) (β : Γ(W.left, ⊤)) :
    finiteEtaleSectionValue W ξ ((FiniteEtale.fiber ξ).map (ρ g).asIso.hom x) β =
      finiteEtaleSectionValue W ξ x ((ρ g).asIso.hom.left.appTop β) := by
  have hn :
      (FiniteEtale.fiberObjEquivHom ξ W ((FiniteEtale.fiber ξ).map (ρ g).asIso.hom x)).left =
        (FiniteEtale.fiberObjEquivHom ξ W x).left ≫ (ρ g).asIso.hom.left :=
    (congrArg (fun f : Over.mk ξ ⟶ W.toComma => f.left)
      (FiniteEtale.fiberObjEquivHom_naturality ξ (ρ g).asIso.hom x)).symm
  exact congrArg (Scheme.ΓSpecIso (.of Ω)).hom
    ((congrArg (fun f : Spec (.of Ω) ⟶ W.left => f.appTop β) hn).trans
      (ConcreteCategory.congr_hom (Scheme.Hom.comp_appTop
        (FiniteEtale.fiberObjEquivHom ξ W x).left (ρ g).asIso.hom.left) β))

variable [CharP Ω p] [Torsor G ((FiniteEtale.fiber ξ).obj W)]
  (haction : ∀ (g : G) (x : (FiniteEtale.fiber ξ).obj W),
    g • x = (FiniteEtale.fiber ξ).map (ρ g).asIso.hom x)

include haction in
omit [Fintype G] in
/-- The section coordinate gives precisely the displacement of the original
fundamental-group action on the original cover fiber, with its sign fixed by
pullback along the specified deck automorphisms. -/
theorem artinSchreierSection_monodromy_displacement
    (χ : G →* Multiplicative (ZMod p)) (β : Γ(W.left, ⊤))
    (hβ : ∀ g, (ρ g).asIso.hom.left.appTop β - β =
      (ZMod.castHom (dvd_refl p) Γ(W.left, ⊤)) (χ g).toAdd)
    (x : (FiniteEtale.fiber ξ).obj W) (γ : Aut (FiniteEtale.fiber ξ)) :
    finiteEtaleSectionValue W ξ (γ • x) β - finiteEtaleSectionValue W ξ x β =
      (ZMod.castHom (dvd_refl p) Ω) (χ ((γ • x) /ₛ x)).toAdd := by
  let d : G := (γ • x) /ₛ x
  have hd : γ • x = (FiniteEtale.fiber ξ).map (ρ d).asIso.hom x :=
    (sdiv_smul (γ • x) x).symm.trans (haction d x)
  have heval : finiteEtaleSectionValue W ξ (γ • x) β =
      finiteEtaleSectionValue W ξ x ((ρ d).asIso.hom.left.appTop β) :=
    (congrArg (fun y => finiteEtaleSectionValue W ξ y β) hd).trans
      (finiteEtaleSectionValue_deck W ρ ξ d x β)
  change finiteEtaleSectionValue W ξ (γ • x) β - finiteEtaleSectionValue W ξ x β =
    (ZMod.castHom (dvd_refl p) Ω) (χ d).toAdd
  rw [heval, ← map_sub, hβ]
  simp only [ZMod.castHom_apply, ZMod.cast_eq_val, map_natCast]

include haction in
omit [Fintype G] [CharP Γ(W.left, ⊤) p] [CharP Ω p] [IsSepClosed Ω] in
/-- The original monodromy commutes with the specified torsor action because
its translations are actual morphisms of the finite étale cover. -/
theorem finiteEtaleDeckAction_commutes :
    SMulCommClass (Aut (FiniteEtale.fiber ξ)) G ((FiniteEtale.fiber ξ).obj W) := by
  constructor
  intro γ g x
  rw [haction, haction]
  exact ConcreteCategory.congr_hom (γ.asIso.hom.naturality (ρ g).asIso.hom) x

include haction in
omit [Fintype G] in
/-- In the existing continuous-character API, the same evaluation difference
is the image of the original torsor character. -/
theorem artinSchreierSection_torsorCharacter [TopologicalSpace G]
    (χ : G →* Multiplicative (ZMod p)) (β : Γ(W.left, ⊤))
    (hβ : ∀ g, (ρ g).asIso.hom.left.appTop β - β =
      (ZMod.castHom (dvd_refl p) Γ(W.left, ⊤)) (χ g).toAdd)
    (x : (FiniteEtale.fiber ξ).obj W) (γ : Aut (FiniteEtale.fiber ξ)) :
    let _ : SMulCommClass (Aut (FiniteEtale.fiber ξ)) G
        ((FiniteEtale.fiber ξ).obj W) := finiteEtaleDeckAction_commutes W ρ ξ haction
    finiteEtaleSectionValue W ξ (γ • x) β - finiteEtaleSectionValue W ξ x β =
      (ZMod.castHom (dvd_refl p) Ω)
        (χ (torsorCharacter (G := Aut (FiniteEtale.fiber ξ)) x γ)).toAdd := by
  intro
  exact artinSchreierSection_monodromy_displacement W ρ p ξ haction χ β hβ x γ

include haction in
/-- Every deck character has a trace-one Artin–Schreier section whose values
recover the actual geometric monodromy. No character comparison is an input. -/
theorem exists_artinSchreierSection_monodromy_of_trace_one
    (t : Γ(W.left, ⊤)) (ht : ∑ g, (ρ g).asIso.hom.left.appTop t = 1)
    (χ : G →* Multiplicative (ZMod p)) :
    ∃ β : Γ(W.left, ⊤),
      (∀ g, (ρ g).asIso.hom.left.appTop (β ^ p - β) = β ^ p - β) ∧
      ∀ (x : (FiniteEtale.fiber ξ).obj W) (γ : Aut (FiniteEtale.fiber ξ)),
        finiteEtaleSectionValue W ξ (γ • x) β - finiteEtaleSectionValue W ξ x β =
          (ZMod.castHom (dvd_refl p) Ω) (χ ((γ • x) /ₛ x)).toAdd := by
  obtain ⟨β, hβ, hinv⟩ := exists_artinSchreierSection_of_trace_one W ρ p t ht χ
  exact ⟨β, hinv, artinSchreierSection_monodromy_displacement W ρ p ξ haction χ β hβ⟩

end Fiber

end EtaleFundamentalGroups.Cohomology
