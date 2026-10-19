# Tori, abelian schemes and semiabelian varieties

These modules use actual `CommGrp (Over S)` group schemes and their existing structure
maps. They form part of `Nyll.SchemeTheory` and do not depend on curve or Jacobian code.
Import the leaf needed by a proof; `Nyll.SchemeTheory.GroupSchemes.All` is the aggregate.

| Interface | Meaning and main operations |
| --- | --- |
| `IsAbelianScheme G` | The structure map is smooth, proper and geometrically connected. Stable under actual group isomorphisms, products and arbitrary scheme base change. |
| `GroupSchemes.splitTorus R r` | The split torus with integral character module `Fin r → ℤ`, constructed using its Hopf algebra. |
| `IsSplitTorus G`, `IsTorus G` | An actual split model, respectively a fixed finite-rank geometric form over a field. |
| `SemiabelianExtension G` | A torus inclusion and smooth surjective homomorphism to an abelian variety, with the identity-kernel universal property. |
| `IsSemiabelian G` | Existence of such an actual extension. |

`GroupSchemes.baseChange f` is the usual group pullback functor; its carrier is the
literal scheme fibre product. `IsTorus.baseChange` and `IsSemiabelian.baseChange`
apply to every field extension. The isomorphism transport lemmas are named `of_iso`
and `iso_iff` in the corresponding property namespace.

For an extension `E`, `E.point_exact T` describes its kernel on every parameter
scheme `T`. Given one lift `x : T ⟶ G.X`, `E.pointFiberEquiv T x` identifies all lifts
of its image with `T ⟶ E.torus.X`. Its forward map multiplies the original inclusion
by `x`, and `pointFiberEquiv_naturality` gives compatibility with changing `T`.
This does not assert surjectivity on rational points over arbitrary fields.

`SemiabelianExamples` constructs the rank-zero kernel extension of an abelian
variety, so `IsAbelianScheme G` supplies `IsSemiabelian G`. The constructed ordinary
Jacobians, and generalized Jacobians of modulus degree zero or one, receive the
abelian-scheme interface in
[`Generalized.AbelianSchemeExamples`](../../JacobianVarieties/Generalized/AbelianSchemeExamples.lean).

[`Generalized.ReducedModulusSemiabelian`](../../JacobianVarieties/Generalized/ReducedModulusSemiabelian.lean)
proves the general result for a **geometrically reduced** modulus, using the
constructed identification of the actual affine kernel with a torus.

`SplitTorusPoints` identifies affine-test points with tuples of units;
`SplitTorusSchemePoints` gives the same natural equivalence for global units on
any parameter scheme. `TorusProduct` constructs the product split model with
sum of ranks and proves product stability for tori.

`SemiabelianProduct` constructs the actual product extension and proves
`IsSemiabelian.product`. `SemiabelianGeometry`, `SemiabelianNoetherian` and
`SemiabelianIntegral` provide geometric connectedness, separation,
quasi-compactness, Noetherianity and geometric integrality for the middle group.
The quotient projection has geometrically integral fibres. `Translation`
constructs actual relative translation isomorphisms and their composition and
homomorphism compatibility.

`VectorGroup` constructs actual additive affine group schemes. In the separate
`SchemeTheory.Affine.WeilRestriction` library, `NilpotentUnitScheme` represents
the full nilpotent tensor-unit kernel and `NilpotentUnitKernelSquare` proves its
identity-kernel universal property for the actual unit restriction map.
`NilpotentIdealGroup` constructs this group for any nilpotent ideal in a finite
commutative algebra over a field, with smoothness and geometric integrality.
`NilpotentUnitLogarithm` gives the actual vector-group exponential/logarithm
isomorphism in characteristic zero. `SquareZeroUnitGroup` gives the corresponding
vector-group isomorphism for a square-zero ideal in every characteristic.

`SchemeTheory.CategoryTheory.PointedTorsorCoordinates` and `PointedTorsorMap`
construct actual torsor coordinates and equivariant morphisms, with the prescribed
point, uniqueness and change-of-origin formulas.
