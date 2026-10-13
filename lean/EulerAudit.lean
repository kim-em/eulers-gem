import EulersGem.UnconditionalEuler
import EulersGem.PolytopeFaces
import Results
import Lean.Util.CollectAxioms

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Lean in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules := #[`EulersGem.LinearInequalities, `EulersGem.PolyhedralRepresentation,
    `EulersGem.PolytopeHalfspaces, `EulersGem.UnconditionalEuler]
  let results := #[``Results.results_euler_characteristic,
    ``Results.results_euler_relation_dimension_three, ``Results.results_euler_polyhedron,
    ``EulersGem.facesOfDim_finite_of_isPolytope]
  let mut count : ℕ := 0
  for (decl, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? decl | continue
    let origin := env.header.moduleNames[idx.toNat]!
    if modules.contains origin || results.contains decl then
      count := count + 1
      for ax in (← collectAxioms decl) do
        unless allowed.contains ax do
          throwError "{decl} depends on an unexpected axiom: {ax}"
  unless count > 0 do
    throwError "No declarations were audited"
  logInfo m!"Axiom audit passed for {count} representation and Euler declarations."

#print axioms EulersGem.IsPolytope.isPolyhedron
#print axioms Results.results_euler_characteristic
#print axioms Results.results_euler_relation_dimension_three
#print axioms Results.results_euler_polyhedron

example {p : Set (EuclideanSpace ℝ (Fin 3))}
    (hp : EulersGem.IsPolytope p) (hdim : EulersGem.affDim p = 3) :
    ({f : Set (EuclideanSpace ℝ (Fin 3)) |
      EulersGem.IsFaceOf p f ∧ EulersGem.affDim f = 0}.ncard : ℤ) -
    ({f : Set (EuclideanSpace ℝ (Fin 3)) |
      EulersGem.IsFaceOf p f ∧ EulersGem.affDim f = 1}.ncard : ℤ) +
    ({f : Set (EuclideanSpace ℝ (Fin 3)) |
      EulersGem.IsFaceOf p f ∧ EulersGem.affDim f = 2}.ncard : ℤ) = 2 :=
  Results.results_euler_polyhedron hp hdim

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {p : Set E} (hp : EulersGem.IsPolytope p) :
    ∃ H : Set (EulersGem.Hyperplane E), H.Finite ∧
      p = ⋂ h ∈ H, EulersGem.closedHalfspace h.1 h.2 :=
  hp.isPolyhedron

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {p : Set E} (hp : EulersGem.IsPolytope p) (d : ℤ) :
    {f : Set E | EulersGem.IsFaceOf p f ∧ EulersGem.affDim f = d}.Finite :=
  EulersGem.facesOfDim_finite_of_isPolytope hp d
