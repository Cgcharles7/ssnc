import random 

def generate_gph2(size, mind): 
    graph = [[0] * size for _ in range(size)] # Add edges to ensure minimum degree 
    for i in range(size): 
        outgoing_edges = 0 
    while outgoing_edges < mind: 
        rem = [k for k in range(size) if k != i and graph[i][k] == 0 and graph[k][i] == 0] if not rem: break target = random.choice(rem) graph[i][target] = 1 outgoing_edges += 1 if outgoing_edges < mind: print(f"Node {i} could not be assigned {mind} outgoing edges.") return graph 
