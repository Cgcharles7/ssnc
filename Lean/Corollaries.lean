-- Defining the state of layer k+1 for 4 corollaries 
variable (h_decay : (bfsLayerVerts G v₀ (k + 1)).card = delta G - k)
variable (h_regular : ∀ v ∈ bfsLayerVerts G v₀ (k + 1), (interiorNeighbors (k + 1) k u_k v).card = k)
variable (h_no_extra : totalInteriorArcs G v₀ (k + 1) = (bfsLayerVerts G v₀ (k + 1)).card * k)
