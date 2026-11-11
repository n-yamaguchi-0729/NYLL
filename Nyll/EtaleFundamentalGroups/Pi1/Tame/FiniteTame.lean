/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Pi1.GaloisCategories.TrivialMonodromy
public import Nyll.EtaleFundamentalGroups.Pi1.FiniteEtale.GaloisCategory
public import Nyll.EtaleFundamentalGroups.GeometricFiber.GenericPointSurjective
public import Nyll.EtaleFundamentalGroups.Inertia.Tame.BoundaryWildQuotient
public import Nyll.SchemeTheory.Normalization.FiniteSeparable

/-!
# Finite tame covers of a smooth curve pair

For an open immersion `j : U ⟶ X` into a smooth integral curve over `k`, a
finite étale cover of `U` is tame along `X ∖ U` when every actual boundary
wild inertia group acts trivially on its geometric generic fibre. We use the
canonical separable closure of `U.functionField`, so no auxiliary generic
field or normalization prime is an argument of the category.

`FiniteTame c j` is the full subcategory of these original finite étale
covers. Its finite limits, finite coproducts, finite group quotients and
fibre functors are inherited from the proved trivial-monodromy construction.
When `X` is proper, this is the tame-cover category for the compactified curve.
The boundary remains explicit for nonproper `X`.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale TopologicalSpace
open CategoryTheory.PreGaloisCategory
open scoped FintypeCatDiscrete

namespace EtaleFundamentalGroups.Tame

universe u

/-- The original generic-point source of an integral scheme is dominant. -/
theorem genericSourceDominant (U : Scheme.{u}) [IsIntegral U] :
    IsDominant (U.fromSpecStalk (genericPoint U)) := genericPoint_isDominant U

attribute [local instance] AlgebraicGeometry.FiniteEtale.genericPoint_isDominant

variable {k : Type u} [Field k] {X U : Scheme.{u}} [IsIntegral X] [IsIntegral U]
  (c : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 c]
  (j : U ⟶ X) [IsOpenImmersion j]

local notation "η" => Spec.map
  (CommRingCat.ofHom (algebraMap U.functionField (SeparableClosure U.functionField))) ≫
  U.fromSpecStalk (genericPoint U)
local notation "N" => boundaryWildKernel k U.functionField
  (SeparableClosure U.functionField) c j (U.fromSpecStalk (genericPoint U))

/-- A finite étale cover is tame at the specified boundary if the actual
boundary wild inertia acts trivially on its original generic fibre. -/
abbrev IsTame : ObjectProperty (FiniteEtale U) := trivialMonodromy (fiber η) N

local instance isTame_isGaloisSubcategory : (IsTame c j).IsGaloisSubcategory :=
  trivialMonodromy_isGaloisSubcategory (fiber η) N

/-- The closed normal kernel condition is equivalent to pointwise triviality
of each original normalization wild image at every closed boundary point. -/
theorem isTame_iff (W : FiniteEtale U) :
    IsTame c j W ↔
      ∀ (x : X) (hx : IsClosed ({x} : Set X)), x ∉ Set.range j →
        ∀ γ ∈ normalizationWildImageAt k U.functionField
          (SeparableClosure U.functionField) c j (U.fromSpecStalk (genericPoint U)) x hx,
          ∀ a : (fiber η).obj W, γ • a = a := by
  change trivialMonodromy (fiber η) N W ↔ _
  rw [trivialMonodromy_iff_le_ker_fiberMonodromy, boundaryWildKernel_le_ker_iff]
  constructor
  · intro h x hx hboundary γ hγ a
    exact congrArg (fun q : Aut ((fiber η).obj W) => q.asIso.hom a) (h x hx hboundary γ hγ)
  · intro h x hx hboundary γ hγ
    apply Aut.ext
    apply Iso.ext
    apply FintypeCat.hom_ext
    exact h x hx hboundary γ hγ

/-- Finite tame covers and their original morphisms over the open curve. -/
abbrev FiniteTame := (IsTame c j).FullSubcategory

/-- Forgetting tameness keeps the finite étale cover and every morphism unchanged. -/
abbrev tameInclusion : FiniteTame c j ⥤ FiniteEtale U := (IsTame c j).ι

/-- The fibre of a tame cover at a geometric point is its usual geometric fibre. -/
abbrev tameFiber {Ω : Type u} [Field Ω] (x : Spec (.of Ω) ⟶ U) :
    FiniteTame c j ⥤ FintypeCat.{u} :=
  tameInclusion c j ⋙ fiber x

/-- Finite tame covers, with their original geometric fibre functor, form a
Galois category. The instance follows from proved categorical closure properties. -/
theorem finiteTame_galoisCategory : GaloisCategory (FiniteTame c j) := inferInstance

/-- Every geometric point supplies a fibre functor on the same tame-cover category. -/
theorem tameFiber_fiberFunctor {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ U) : FiberFunctor (tameFiber c j x) := inferInstance

/-- The tame fundamental group is the automorphism group of the geometric
fibre functor on finite tame covers, with its canonical profinite topology. -/
notation:arg "π₁ᵗ" "(" c ", " j ", " x ")" => Aut (tameFiber c j x)

/-- The tame-cover Galois category is equivalent to continuous finite actions
of its actual fibre-functor automorphism group. -/
def tameCoverActionEquivalence {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ U) :
    FiniteTame c j ≌ ContAction FintypeCat.{u} π₁ᵗ(c, j, x) :=
  (functorToContAction (tameFiber c j x)).asEquivalence

end EtaleFundamentalGroups.Tame
