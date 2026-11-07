import SSNC

theorem seymour_second_neighborhood
    (G : FiniteGraph) (hG : G.IsOriented) (hne : G.vertices.Nonempty) :
    ∃ u ∈ G.vertices, G.IsSeymourProp u :=
  SSNC.Contradiction.seymourEmergence G hG hne
