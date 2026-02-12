import Mathlib
import YM.SpectralStability.RescaledNRC
import YM.OSPositivity.Clustering
import YM.OSPositivity.LocalFields
import YM.OSPositivity.Wightman

/--
TeX anchors ↔ Lean symbols (lightweight acceptance map, build-checked).

References (Yang-Mills-sept21.tex):
- NRC(all nonreal z): lines 5339–5357.
- OS3/OS5 mapping (gap ⇒ clustering, OS→Wightman context): lines 4466–4476.

Intent: ensure cited anchors have concrete Lean symbols in this repo.
Implementation: `#check` smoke tests; the build fails if symbols are missing.
-/
namespace YM.Docs.Anchors

-- NRC (all nonreal z): cf. lines 5339–5357
#check YM.SpectralStability.RescaledNRC.NRC_all_nonreal
#check YM.SpectralStability.RescaledNRC.NRC_all_nonreal_holds

-- Gap ⇒ Clustering (OS3): cf. lines 4466–4476
#check YM.OSPositivity.Clustering.clusters
#check YM.OSPositivity.Clustering.clusters_of_positive_gap
#check YM.OSPositivity.Clustering.clusters_from_gap

-- OS positivity (local fields) and Wightman spectrum condition: cf. lines 4466–4476
#check YM.OSPositivity.LocalFields.build_local_field_os_positive
#check YM.OSPositivity.Wightman.build_wightman_field_satisfies

end YM.Docs.Anchors


