use List;
use IO;
use Time; 

// Define the number of vertices and edges
config const numberOfVertices = 10;
config const numberOfEdges = 100;

// Global counter for isomorphisms
var globalIsoCounter: atomic int;

// Graph data structure
record Graph {
    var numVertices: int;  // Number of vertices
    var numEdges: int;  // Number of edges
    var adjacencyList: [1..numVertices] list(int);  // Adjacency list
    var nodeLabels: [1..numVertices] string;  // Labels for nodes
    var edgeLabels: [1..numVertices, 1..numVertices] string; // Labels for edges
    var nodeDegree: [1..numVertices] int; // Count of neighbors for each node
    //check tit again
    // Initialize the graph with vertices and an adjacency list filled with empty lists
    proc init(numVertices: int, numEdges: int) {
        this.numVertices = numVertices;
        this.numEdges = numEdges;
        edgeLabels = "Grey"; // Initial edge color set to Grey
        nodeDegree = 0; // Initialize all nodes as having no neighbors
    }

    // Method to add a label to a node
    proc addNodeLabel(nodeIndex: int, Tlabel: string) {
        if nodeIndex >= 1 && nodeIndex <= this.numVertices {
            nodeLabels[nodeIndex] = Tlabel;
        } 
    }

    // Method to add a label to an edge
    proc addEdgeLabel(i: int, j: int, Tlabel: string) {
        if i >= 1 && i <= this.numEdges && j >= 1 && j <= this.numEdges {
            edgeLabels[i, j] = Tlabel;
            nodeDegree[i] += 1; // Node i has at least one neighbor (j)
            nodeDegree[j] += 1; // Node j has at least one neighbor (i)
        }
    }
}

// Function to check if the vertex v of H can be added to the current mapping
// Returns true if it can be added, false otherwise
proc isIsomorphic(G: Graph, H: Graph, v: int, mapping: [?D] int): bool {
    var i = mapping[v];  // Vertex i in G corresponds to vertex v in H

    // Check if the node labels are the same
    if H.nodeLabels[v] != G.nodeLabels[i] {
        return false;
    }

    // Check if the in-degree + out-degree of every vertex in H is less than or equal to 
    // the corresponding vertex in G
    for u in 1..v {
        if mapping[u] > 0 {  // If u in H is mapped to some vertex in G
            // Check if there is an edge from u to v in H
            if H.adjacencyList[u].contains(v) {
                // Check if there is an edge from mapping[u] to mapping[v] in G
                // And check if the edge labels are the same
                if !G.adjacencyList[mapping[u]].contains(mapping[v]) || 
                   H.edgeLabels[u, v] != G.edgeLabels[mapping[u], mapping[v]] {
                    return false;
                }
            }

            // Check if there is an edge from v to u in H
            if H.adjacencyList[v].contains(u) {
                // Check if there is an edge from mapping[v] to mapping[u] in G
                // And check if the edge labels are the same
                if !G.adjacencyList[mapping[v]].contains(mapping[u]) ||
                   H.edgeLabels[v, u] != G.edgeLabels[mapping[v], mapping[u]] {
                    return false;
                }
            }
        }
    }
    return true;
}

// Recursive function for Ullmann's subgraph isomorphism algorithm
proc ullmannSubgraphIsomorphism11Helper(G: Graph, H: Graph, v: int, visited: [?D1] bool, mapping: [?D2] int): list([1..H.numVertices] int) {
    var isomorphismList: list(list(int));

    var localIsoList: list([1..H.numVertices] int);  // List to store the isomorphisms found in the current branch
    var localIsoCounter = 0;  // Count the number of isomorphisms found in the current branch

    for i in 1..G.numVertices {
        if (!visited[i] && G.nodeDegree[i] >= 1) { 
            visited[i] = true;  // Mark the vertex as visited
            mapping[v] = i;  // Add the vertex to the current mapping
            // If the vertex can be added to the current mapping
            if (isIsomorphic(G, H, v, mapping)) {
                // If all vertices in H have been visited
                if (v >= H.numVertices) {
                    var isComplete = true;  // Check if all vertices in the subgraph have been mapped
                    for j in 1..H.numVertices {
                        if (mapping[j] < 1) {
                            isComplete = false;
                            break;
                        }
                    }
                    // If the mapping is complete, add the current mapping to the isomorphism list
                    if (isComplete) {
                        localIsoList.pushBack(mapping);
                    }
                }
                else {
                    // Recursively call the function for the next vertex
                    var subIsoList = ullmannSubgraphIsomorphism11Helper(G, H, v+1, visited, mapping);
                    if (subIsoList.size > 0) {
                        // Add isomorphisms found in the sub-branch to the current isomorphism list
                        for isoMapping in subIsoList {
                            localIsoList.pushBack(isoMapping);
                        }
                    }
                }
            }
            // Backtrack: unvisit the vertex and remove it from the mapping
            visited[i] = false;
            mapping[v] = -1;
        }
    }
    return localIsoList;  // Return the list of isomorphisms found in the current branch
}

// Ullmann's subgraph isomorphism algorithm
proc ullmannSubgraphIsomorphism11(G: Graph, H: Graph) {

    // Create an array to hold the vertices sorted by degree
    var subGraphVerticesSortedByDegree: [1..H.numVertices] int;
    for v in 1..H.numVertices {
        subGraphVerticesSortedByDegree[v] = v;
    }

    // Sort the array based on degrees in descending order
    for i in 1..H.numVertices {
        for j in i+1..H.numVertices {
            if H.nodeDegree[subGraphVerticesSortedByDegree[i]] < H.nodeDegree[subGraphVerticesSortedByDegree[j]] {
                var tmp = subGraphVerticesSortedByDegree[i];
                subGraphVerticesSortedByDegree[i] = subGraphVerticesSortedByDegree[j];
                subGraphVerticesSortedByDegree[j] = tmp;
            }
        }
    }

    // Parallelize over the vertices of subGraph based on degree order!
    //Chek it realy changes the running time? I have doubt. because of parallelism!
    coforall idx in 1..H.numVertices {
        var v = subGraphVerticesSortedByDegree[idx];
        writeln("idx is: ",idx, " v is: ",v);
        var visited: [1..G.numVertices] bool;  // Array to keep track of visited vertices
        var mapping: [1..H.numVertices] int;  // Array for the current mapping
        mapping = -1;  // Initialize the mapping array to -1 (indicating no mapping)
        visited = false;  // Initialize all vertices as unvisited
        // Find isomorphisms for the current vertex v
        var subIsoList = ullmannSubgraphIsomorphism11Helper(G, H, v, visited, mapping);
        if (subIsoList.size > 0) {
            // Print isomorphisms found by the current task without merging
            //writeln("Isomorphisms found by task ", v, ":");
            var taskIsoCounter = 0;
            for isoMapping in subIsoList {
                taskIsoCounter += 1;
                writeln("Isomorphism #", taskIsoCounter, ":");
                for k in 1..H.numVertices {
                    var mappedVertex = isoMapping[k];
                    if (mappedVertex > 0) {
                        writeln("Subgraph vertex ", k, " -> Graph vertex ", mappedVertex);
                    }
                }
                //writeln("----");
            }
            
            // Add the number of isomorphisms found by the current task to the global counter
            globalIsoCounter.add(taskIsoCounter);
        }
    }
 
    // Print the total number of isomorphisms found
    writeln("Total isomorphisms found: ", globalIsoCounter.read());
}


// Function to read graph data from a file and return a new Graph object
proc readGraphFromFile(filename: string, GraphNumVertices: int, GraphNumEdges: int): Graph {
    var myFile = open(filename, ioMode.r);
    var myFileReader = myFile.reader();

    var graph = new Graph(GraphNumVertices, GraphNumEdges);
    var line: string;
    while (myFileReader.readLine(line)) {
        var tokens = line.split(" ");

        if tokens[0] == "v" {
            var nodeIndex = (tokens[1]: int);
            var nodeLabel = tokens[2];
            graph.addNodeLabel(nodeIndex, nodeLabel);
        } else if tokens[0] == "e" {
            var i = (tokens[1]: int);
            var j = (tokens[2]: int);
            var edgeLabel: string = tokens[3];

            graph.adjacencyList[i].pushBack(j); // Add only one direction for directed graph
            
            graph.addEdgeLabel(i, j, edgeLabel); // Add edge label only for the specified direction
        }
    }
    myFileReader.close();
    myFile.close();

    return graph;
}

proc degreeCheck(G: Graph, H: Graph) {
    var maxDegreeG = 0;
    var maxDegreeH = 0;
    
    // Calculate max degree of G
    for i in 1..G.numVertices {
        var degree = G.adjacencyList[i].size;
        if degree > maxDegreeG {
            maxDegreeG = degree;
        }
    }

    // Calculate max degree of H
    for i in 1..H.numVertices {
        var degree = H.adjacencyList[i].size;
        if degree > maxDegreeH {
            maxDegreeH = degree;
        }
    }

    // Compare max degrees
    if (maxDegreeH <= maxDegreeG) then {
        writeln(" Maximum degree in main graph and subgraph ckecked,"); 
        writeln("Isomorphism may be possible...");
        return;
    } else {
        writeln("No isomorphism possible." );
        return;
       }
    }

proc countNodesWithoutNeighbors(G: Graph) {
    var count: int = 0;  // Initialize the counter
    var nodes: list(int);  // List to store the nodes with no neighbors

    // Loop through each node
    for i in 1..G.numVertices {
        if (G.nodeDegree[i]== 0) {  // If the node has no neighbors
            count += 1;  // Increment the counter
            nodes.pushBack(i);  // Add the node to the list
        }
    }

    // Display the result
    writeln(" Search domain reduced ", count, " nodes.");
    writeln("no neighbors nodes removed...");
}
// Function for degree filtering
proc degreeFiltering(G: Graph, H: Graph): bool {
    for i in 1..H.numVertices {
        var degreeH = H.adjacencyList[i].size;
        var validMappingExists = false;
        for j in 1..G.numVertices {
            var degreeG = G.adjacencyList[j].size;
            // In-degree and out-degree of the vertex in H is less than or equal to 
            // the corresponding vertex in G
            if degreeH <= degreeG {
                validMappingExists = true;
                break;
            }
        }
        // If no valid mapping for a vertex in H exists, return false
        if !validMappingExists {
            writeln("No isomorphism possible due to degree filtering.");
            return false;
        }
    }
    // If a valid mapping for every vertex in H exists, return true
    writeln("Degree filtering passed. Isomorphism may be possible...\n"); 
    return true;
}

// Function to remove nodes with no input or output edges and return the reduced graph
proc removeIsolatedNodes(graph: Graph): (Graph, [1..graph.numVertices] int) {
    var mapping: [1..graph.numVertices] int; // Mapping of old indices to new ones

    // Find nodes with no input or output edges
    var isolatedNodes: [1..graph.numVertices] bool;
    for i in 1..graph.numVertices {
        if graph.nodeDegree[i] == 0 {
            isolatedNodes[i] = true;
            //writeln("Node ", i, " is isolated.");
        }
    }

    // Initialize the mapping
    var newIndex = 1;
    for i in 1..graph.numVertices {
        if !isolatedNodes[i] {
            mapping[i] = newIndex;
            newIndex += 1;
        } else {
            mapping[i] = -1;
        }
    }

    // Create the reduced graph and add nodes that can be in reduced graph with their labels
    var reducedGraph = new Graph(newIndex - 1, graph.numEdges);
    for i in 1..graph.numVertices {
        if !isolatedNodes[i] {
            var nodeLabel = graph.nodeLabels[i];
            reducedGraph.addNodeLabel(mapping[i], nodeLabel);
            for j in graph.adjacencyList[i] {
                if !isolatedNodes[j] {
                    var edgeLabel = graph.edgeLabels[i, j];
                    reducedGraph.addEdgeLabel(mapping[i], mapping[j], edgeLabel);
                    reducedGraph.adjacencyList[mapping[i]].pushBack(mapping[j]);
                }
            }
        }
    }

    // Print the number of isolated nodes and reduced node count
    var numIsolatedNodes = graph.numVertices - (newIndex - 1);
    writeln("No neighbors nodes removed. Total isolated nodes: ", numIsolatedNodes);
    writeln("Reduced graph generated and we will go on with that...");

    return (reducedGraph, mapping);
}
// Function to check if subgraph node and edge labels are present in the main graph
proc checkLabelsMatch(mainGraph: Graph, subGraph: Graph): bool {
    for i in 1..subGraph.numVertices {
        var subGraphNodeLabel = subGraph.nodeLabels[i];
        var labelFound = false;
        for j in 1..mainGraph.numVertices {
            if mainGraph.nodeLabels[j] == subGraphNodeLabel {
                labelFound = true;
                break;
            }
        }
        if !labelFound {
            writeln("Subgraph node label '", subGraphNodeLabel, "' not found in main graph.");
            return false;
        }
    }

    for i in 1..subGraph.numVertices {
        for j in 1..subGraph.numVertices {
            var subGraphEdgeLabel = subGraph.edgeLabels[i, j];
            if subGraphEdgeLabel != "Grey" {
                var labelFound = false;
                for u in 1..mainGraph.numVertices {
                    for v in 1..mainGraph.numVertices {
                        if mainGraph.edgeLabels[u, v] == subGraphEdgeLabel {
                            labelFound = true;
                            break;
                        }
                    }
                    if labelFound {
                        break;
                    }
                }
                if !labelFound {
                    writeln("Subgraph edge label '", subGraphEdgeLabel, "' not found in main graph.");
                    return false;
                }
            }
        }
    }

    return true;
}


// Main function
proc main() {
    
    // Define the main graph and subgraph  
    var mainGraph = new Graph(32, 41);
    mainGraph = readGraphFromFile("graph.txt", 32, 41);
    writeln(mainGraph.adjacencyList);

    // Define the subgraph    
    var subGraph = new Graph(4, 4);
    subGraph = readGraphFromFile("subgraph.txt", 4 , 4);

   
    //Preprocessing
    writeln("\nPreprocessing step 1:\n"); 
    
    degreeCheck(mainGraph, subGraph);

    writeln("\nPreprocessing step 2:\n"); 

    // Count and display nodes without neighbors in the main graph
    //countNodesWithoutNeighbors(mainGraph);
      // Find and remove isolated nodes from the main graph
    var (reducedGraph, indexMapping) = removeIsolatedNodes(mainGraph);
    

    writeln("\nPreprocessing step 3:\n"); 

    //degreeFiltering(mainGraph, subGraph);

    writeln("********************************************");
    // Timer for running the Algorithm 
    var timer:stopwatch;
    timer.start();
        
    ullmannSubgraphIsomorphism11(mainGraph, subGraph);
    // Print out the length of time it takes to find and print out the isomorphism.
    timer.stop();
    var outputMessage: string = "Running the algorithm to find out the isomorphism " + timer.elapsed():string + " sec";
    writeln("\n\n", outputMessage);
    writeln("Including printing on screen!");    

    var timer1:stopwatch;
    if checkLabelsMatch(reducedGraph, subGraph) && degreeFiltering(reducedGraph, subGraph){
       writeln("Labels matched.");
       timer1.start();
       ullmannSubgraphIsomorphism11(reducedGraph, subGraph);
       timer1.stop();
    } else {
          writeln("Labels do not match. Isomorphism check skipped.");
        }
    
    // Print out the length of time it takes to find and print out the isomorphism.
    outputMessage = "Running the algorithm with reduced graph " + timer1.elapsed():string + " sec";
    writeln("\n\n", outputMessage);
    writeln("Including printing on screen!");
    writeln("end of the running.");
}
