import random 

def generate_gph2(size, mind): 
    graph = [[0] * size for _ in range(size)] # Add edges to ensure minimum degree 
    for i in range(size): 
        outgoing_edges = 0 
    while outgoing_edges < mind: 
        rem = [k for k in range(size) if k != i and graph[i][k] == 0 and graph[k][i] == 0] if not rem: break target = random.choice(rem) graph[i][target] = 1 outgoing_edges += 1 if outgoing_edges < mind: print(f"Node {i} could not be assigned {mind} outgoing edges.") return graph 

def mindeg(graph): # Find the node with the minimum degree (either outgoing or incoming) min_degree = float('inf') min_node = -1 for i, row in enumerate(graph): degree = sum(row) + sum(col[i] for col in graph)  # Sum of row + column if degree < min_degree: min_degree = degree min_node = i return min_node 

def generate_dg(num_nodes): num_arcs = random.randint(3 * num_nodes, (num_nodes * (num_nodes - 1)) // 2) graph = [[0] * num_nodes for _ in range(num_nodes)] nodes = list(range(num_nodes)) tree = [] # Shu le nodes randomly and create the initial tree while nodes: loc = random.randint(0, len(nodes) - 1) tree.append(nodes.pop(loc)) count = 0 while len(tree) < num_nodes: inside = random.randint(0, len(tree) - 1) outside = random.randint(0, num_nodes - len(tree) - 1) edge_direction = random.choice([1, -1]) if edge_direction == 1: graph[tree[inside]][nodes[outside]] = 1 else: graph[nodes[outside]][tree[inside]] = 1 tree.append(nodes[outside]) count += 1 while count < num_arcs: i = mindeg(graph) rem = [j for j in range(num_nodes) if graph[i][j] == 0 and graph[j][i] == 0 and j != i] if not rem: j = random.randint(0, num_nodes - 1) if j == i: j = (j + 1) % num_nodes graph[i][j] = 1 else: j = random.choice(rem) graph[i][j] = 1 count += 1 return graph

def isoriented(graph): ans = [] for i in range(len(graph)): if graph[i][i] == 1: ans.append(f"{i}, {i}") for j in range(len(graph)): if graph[i][j] == 1 and graph[j][i] == 1: ans.append(f"{i}, {j}") ans.append(f"{j}, {i}") if ans:  # If any oriented edges were found, no need to continue break return ans


def generate_oriented_graph(size, min_out_degree): if size <= 0 or min_out_degree < 0 or min_out_degree >= size: raise ValueError("Invalid parameters: size must be > 0, min_out_degree must be >= 0 and < size.") graph = [] for i in range(size): graph.append([0] * size)  # Initialize all edges to 0 (no edge) for i in range(size): available_nodes = [] for j in range(size): if i != j and graph[j][i] == 0 and graph[i][j] == 0: available_nodes.append(j) for _ in range(min_out_degree): if not available_nodes: break target = random.choice(available_nodes) graph[i][target] = 1  # Add directed edge from i to target available_nodes.remove(target) return graph # Example usage if __name__ == "__main__": size = 5 min_out_degree = 2 oriented_graph = generate_oriented_graph(size, min_out_degree) for row in oriented_graph: print(row) 

def mindeg(graph): def deg(graph): # Calculate the degree of each node degrees = [0] * len(graph) for i in range(len(graph)): degrees[i] = sum(graph[i]) return degrees # Get the degree list degs = deg(graph) if not degs: raise ValueError("The degree list is empty. The graph might be invalid.") # Initialize min degree and its location min_loc = 0 min_deg = degs[min_loc] for i in range(1, len(degs)): if degs[i] < min_deg: min_deg = degs[i] min_loc = i return min_loc 

def square(graph): # Validate input if not isinstance(graph, list) or len(graph) == 0: raise ValueError("The graph should be a non-empty 2D list.") num_nodes = len(graph) for row in graph: if not isinstance(row, list) or len(row) != num_nodes: raise ValueError("The graph should be a square matrix.") # Initialize the new graph new_graph = [[0] * num_nodes for _ in range(num_nodes)] # Compute the square of the graph for i in range(num_nodes): for j in range(num_nodes): if graph[i][j] == 1: for k in range(num_nodes): if graph[j][k] == 1: new_graph[i][k] = 1 return new_graph transitive_triangles = find_transitive_triangles(graph) print(f"Transitive triangles: {transitive_triangles}") 

    


def first_degree_neighbors(node, graph): if not isinstance(graph, list) or not 0 <= node < len(graph): raise ValueError("Invalid node or graph.") neighbors = [i for i, is_connected in enumerate(graph[node]) if is_connected] return neighbors 

def second_degree_neighbors(node, graph): if not isinstance(graph, list) or not 0 <= node < len(graph): raise ValueError("Invalid node or graph.") first_neighbors = first_degree_neighbors(node, graph) second_neighbors = set() for neighbor in first_neighbors: for second_neighbor, is_connected in enumerate(graph[neighbor]): if is_connected and second_neighbor != node: second_neighbors.add(second_neighbor) return list(second_neighbors) 

def decreasing_sequence_property(x, graph): def first_degree_neighbors(node): return [i for i, is_connected in enumerate(graph[node]) if is_connected] def second_degree_neighbors(node): first_neighbors = first_degree_neighbors(node) second_neighbors = set() for neighbor in first_neighbors: for second_neighbor, is_connected in enumerate(graph[neighbor]): if is_connected and second_neighbor != node: second_neighbors.add(second_neighbor) return list(second_neighbors) 

# Compute N+(x) and N++(x) N_plus_x = first_degree_neighbors(x) N_plus_plus_x = second_degree_neighbors(x) # Check decreasing sequence property has_decreasing_property = len(N_plus_x) > len(N_plus_plus_x) def interior_neighbors(y): N_plus_y = first_degree_neighbors(y) return [neighbor for neighbor in N_plus_y if neighbor in N_plus_x] def exterior_neighbors(y): N_plus_y = first_degree_neighbors(y) return [neighbor for neighbor in N_plus_y if neighbor in N_plus_plus_x and neighbor not in N_plus_x] 
# Compute interior and exterior neighbors if x has decreasing sequence property if has_decreasing_property: interior_degrees = {y: len(interior_neighbors(y)) for y in N_plus_x} exterior_degrees = {y: len(exterior_neighbors(y)) for y in N_plus_x} return True, interior_degrees, exterior_degrees else: return False, None, None

# Example usage graph = [ [0, 1, 0, 1],  # Node 0 [0, 0, 1, 0],  # Node 1 [1, 0, 0, 0],  # Node 2 [0, 0, 1, 0]   # Node 3 ] node = 0 has_property, interior_degrees, exterior_degrees = decreasing_sequence_property(node, graph) if has_property: print(f"Node {node} has the decreasing sequence property.") print(f"Interior degrees: {interior_degrees}") 

print(f"Exterior degrees: {exterior_degrees}") else: print(f"Node {node} does not have the decreasing sequence property.")

def find_transitive_triangles(graph): transitive_triangles = [] def first_degree_neighbors(node): return [i for i, is_connected in enumerate(graph[node]) if is_connected] num_nodes = len(graph) for x in range(num_nodes): N_plus_x = first_degree_neighbors(x) for y in N_plus_x: for u in N_plus_x: if y != u and graph[y][u] == 1: transitive_triangles.append((x, y, u)) return transitive_triangles # Example usage graph = [ [0, 1, 0, 1],  # Node 0 [0, 0, 1, 0],  # Node 1 [1, 0, 0, 0],  # Node 2 [0, 0, 1, 0]   # Node 3 ] 

def shortest_path_distance(graph, start): num_nodes = len(graph) distances = [-1] * num_nodes  # Initialize distances with -1 (unreachable) distances[start] = 0 queue = deque([start]) while queue: current = queue.popleft() current_distance = distances[current] for neighbor, is_connected in enumerate(graph[current]): 

if is_connected and distances[neighbor] == -1: distances[neighbor] = current_distance + 1 queue.append(neighbor) return distances # Example usage graph = [ [0, 1, 0, 1],  # Node 0 [0, 0, 1, 0],  # Node 1 [1, 0, 0, 0],  # Node 2 [0, 0, 1, 0]   # Node 3 ] start_node = 0 distances = shortest_path_distance(graph, start_node) print(f"Distances from node {start_node}: {distances}") 

def has_decreasing_sequence_property(graph, node): N_plus = [i for i, is_connected in enumerate(graph[node]) if is_connected] N_plus_plus = set() for neighbor in N_plus: N_plus_plus.update([i for i, is_connected in enumerate(graph[neighbor]) if is_connected]) return len(N_plus) > len(N_plus_plus) 

def distance_k_decreasing_sequence_property(graph, v0, k): def bfs_distance(start): num_nodes = len(graph) distances = [-1] * num_nodes distances[start] = 0 queue = deque([start]) while queue: current = queue.popleft() current_distance = distances[current] for neighbor, is_connected in enumerate(graph[current]): if is_connected and distances[neighbor] == -1: distances[neighbor] = current_distance + 1 queue.append(neighbor) return distances distances = bfs_distance(v0) for node, dist in enumerate(distances): if 1 <= dist <= k and not has_decreasing_sequence_property(graph, node): return False return True 

graph = [ [0, 1, 1, 0],  # Node 0 [0, 0, 1, 0],  # Node 1 [0, 0, 0, 1],  # Node 2 [0, 0, 0, 0]   # Node 3 ] v0 = 0 k = 2 result = distance_k_decreasing_sequence_property(graph, v0, k) print(f"Node {v0} has the distance-{k} decreasing sequence property: {result}") 

def find_seymour_diamonds(graph): num_nodes = len(graph) diamonds = [] for x in range(num_nodes): N_plus_x = [i for i, is_connected in enumerate(graph[x]) if is_connected] for i in range(len(N_plus_x)): for j in range(i + 1, len(N_plus_x)): u1 = N_plus_x[i] u2 = N_plus_x[j] for y in range(num_nodes): if graph[u1][y] == 1 and graph[u2][y] == 1: diamonds.append((x, u1, u2, y)) return diamonds # Example usage graph = [ [0, 1, 1, 0],  # Node 0 [0, 0, 0, 1],  # Node 1 [0, 0, 0, 1],  # Node 2 [0, 0, 0, 0]   # Node 3 ] seymour_diamonds = find_seymour_diamonds(graph) print(f"Seymour diamonds: {seymour_diamonds}") E
def detectBackwardArcs(graph): backwardArcs = [] visited = {node: 'white' for node in graph} def dfs(node): visited[node] = 'gray' for neighbor in graph[node]: if visited[neighbor] == 'gray': backwardArcs.append((node, neighbor)) elif visited[neighbor] == 'white': dfs(neighbor) visited[node] = 'black' for node in graph: if visited[node] == 'white': dfs(node) return backwardArcs

import networkx as nx import matplotlib.pyplot as plt def visualize_graph(graph, backwardArcs): G = nx.DiGraph(graph) pos = nx.spring_layout(G) nx.draw(G, pos, with_labels=True, node_color='lightblue', edge_color='gray') # Draw backward arcs in a di erent color for u, v in backwardArcs: nx.draw_networkx_edges(G, pos, edgelist=[(u, v)], edge_color='red', width=2) plt.show() 


def load_graphs(filename): with open(filename, 'r') as file:  data = json.load(file) return data 

from IPython.display import display, HTML def display_html_table(graph): num_nodes = len(graph) html_content = '<table border="1">' html_content += "<tr><td></td>" for i in range(num_nodes): html_content += f"<td>{i}</td>" html_content += "</tr>" for i in range(num_nodes): html_content += f"<tr><td>{i}</td>" for j in range(num_nodes): html_content += f'<td id="cell_{i}_{j}" onclick="chAdj({i}, {j})">{graph[i][j]}</td>' html_content += "</tr>" html_content += '</table>' display(HTML(html_content)) 

import json import random import networkx as nx from networkx.algorithms import bipartite def generate_graphs(num_graphs, size, min_degree): graphs = [] for _ in range(num_graphs): graph = nx.gnp_random_graph(size, 0.5, directed=True) while not is_valid_graph(graph, min_degree): graph = nx.gnp_random_graph(size, 0.5, directed=True) graphs.append(graph) return graphs def is_valid_graph(graph, min_degree): for node in graph.nodes: if graph.out_degree(node) < min_degree: return False return True def find_min_degree_node(graph): min_node = None min_degree = float('inf') for node in graph.nodes: if graph.out_degree(node) < min_degree: min_degree = graph.out_degree(node) min_node = node return min_node def check_degree_doubling(graph, path): for node in path: if graph.out_degree(node) > 2 * min(graph.out_degree(n) for n in graph.nodes): return True return False def main(): num_graphs = 10000 size = 10 min_degree = 2 graphs = generate_graphs(num_graphs, size, min_degree) for graph in graphs: min_node = find_min_degree_node(graph) if min_node is None: continue 
path = find_decreasing_path(graph, min_node) if path and not check_degree_doubling(graph, path): print(f"Found a graph with no degree doubling: {graph.edges()}") return print("No valid graph found.") if __name__ == "__main__": main() 








        

    
