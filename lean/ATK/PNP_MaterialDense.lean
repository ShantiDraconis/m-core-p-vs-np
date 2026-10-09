import MCore.Material.P01Adapter
namespace ATK.PNP
abbrev Material : Prop := MCore.Material.P01CanonicalMaterial
theorem machine_of_material (h : Material) : MCore.Real.CanonicalSATMachineClosure :=
  MCore.Material.p01_material_closes_sat_machine h
end ATK.PNP
#print axioms ATK.PNP.machine_of_material
