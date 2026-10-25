import java.util.*;

public final class Algorithms {

    private Algorithms() {
    }

    public static List<Integer> reconstructRoute(int source, int target, int[] parentEdges, int[][] edges) {
        if (target == source || target < 0 || target >= parentEdges.length) {
            return Collections.emptyList();
        }

        List<Integer> routeEdges = new ArrayList<>();
        int currentVertex = target;

        while (currentVertex != source && currentVertex != -1) {
            int parentEdgeId = parentEdges[currentVertex];
            if (parentEdgeId == -1) {
                break;
            }
            routeEdges.add(parentEdgeId);

            int u = edges[parentEdgeId][0];
            int v = edges[parentEdgeId][1];
            currentVertex = (v == currentVertex) ? u : v;
        }

        Collections.reverse(routeEdges);
        return routeEdges;
    }

    static Map<String, Object> dsu(Map<String, Object> input) {
        int n = Input.vertexCount(input);
        int[][] operations = Input.operations(input);

        DisjointSet dsuSet = new DisjointSet(n);
        List<List<Integer>> states = new ArrayList<>();

        for (int[] op : operations) {
            int u = op[0];
            int v = op[1];
            dsuSet.union(u, v);
            states.add(Arrays.asList(dsuSet.getComponentCount(), dsuSet.getMaxComponentSize()));
        }

        return Map.of("states", states);
    }

    static Map<String, Object> kruskal(Map<String, Object> input) {
        int n = Input.vertexCount(input);
        int[][] edges = Input.edges(input);

        Integer[] edgeIndices = new Integer[edges.length];
        for (int i = 0; i < edges.length; i++) {
            edgeIndices[i] = i;
        }

        Arrays.sort(edgeIndices, Comparator.comparingInt(a -> edges[a][2]));

        DisjointSet dsuSet = new DisjointSet(n);
        long totalCost = 0;
        List<Integer> usedEdgeIds = new ArrayList<>();

        for (int idx : edgeIndices) {
            int u = edges[idx][0];
            int v = edges[idx][1];
            int weight = edges[idx][2];

            if (dsuSet.union(u, v)) {
                totalCost += weight;
                usedEdgeIds.add(idx);
            }
        }

        return Map.of(
                "cost", totalCost,
                "edge_ids", usedEdgeIds,
                "components", dsuSet.getComponentCount()
        );
    }

    static Map<String, Object> prim(Map<String, Object> input) {
        int n = Input.vertexCount(input);
        int[][] edges = Input.edges(input);

        List<List<Integer>> adj = new ArrayList<>();
        for (int i = 0; i < n; i++) adj.add(new ArrayList<>());
        for (int i = 0; i < edges.length; i++) {
            int u = edges[i][0];
            int v = edges[i][1];
            adj.get(u).add(i);
            adj.get(v).add(i);
        }

        boolean[] visited = new boolean[n];
        long totalCost = 0;
        List<Integer> usedEdgeIds = new ArrayList<>();
        PriorityQueue<EdgeInfo> pq = new PriorityQueue<>(Comparator.comparingInt(e -> e.weight));

        for (int start = 0; start < n; start++) {
            if (visited[start]) continue;
            visited[start] = true;
            for (int edgeId : adj.get(start)) {
                int u = edges[edgeId][0];
                int v = edges[edgeId][1];
                int nextVertex = (u == start) ? v : u;
                pq.add(new EdgeInfo(nextVertex, edges[edgeId][2], edgeId));
            }

            while (!pq.isEmpty()) {
                EdgeInfo curr = pq.poll();
                if (visited[curr.to]) continue;
                visited[curr.to] = true;
                totalCost += curr.weight;
                usedEdgeIds.add(curr.edgeId);

                for (int edgeId : adj.get(curr.to)) {
                    int u = edges[edgeId][0];
                    int v = edges[edgeId][1];
                    int nextVertex = (u == curr.to) ? v : u;
                    if (!visited[nextVertex]) {
                        pq.add(new EdgeInfo(nextVertex, edges[edgeId][2], edgeId));
                    }
                }
            }
        }

        DisjointSet dsu = new DisjointSet(n);
        for (int edgeId : usedEdgeIds) {
            dsu.union(edges[edgeId][0], edges[edgeId][1]);
        }

        return Map.of(
                "cost", totalCost,
                "edge_ids", usedEdgeIds,
                "components", dsu.getComponentCount()
        );
    }

    static Map<String, Object> scc(Map<String, Object> input) {
        int n = Input.vertexCount(input);
        int[][] edges = Input.edges(input);

        List<List<Integer>> adj = new ArrayList<>();
        List<List<Integer>> revAdj = new ArrayList<>();
        for (int i = 0; i < n; i++) {
            adj.add(new ArrayList<>());
            revAdj.add(new ArrayList<>());
        }

        for (int[] e : edges) {
            adj.get(e[0]).add(e[1]);
            revAdj.get(e[1]).add(e[0]);
        }

        boolean[] visited = new boolean[n];
        Deque<Integer> stack = new ArrayDeque<>();
        for (int i = 0; i < n; i++) {
            if (!visited[i]) {
                sccDfs1(i, adj, visited, stack);
            }
        }

        Arrays.fill(visited, false);
        int[] componentLabels = new int[n];
        int compId = 0;
        List<List<Integer>> componentsList = new ArrayList<>();

        while (!stack.isEmpty()) {
            int v = stack.pop();
            if (!visited[v]) {
                List<Integer> comp = new ArrayList<>();
                sccDfs2(v, revAdj, visited, comp);
                Collections.sort(comp);
                componentsList.add(comp);
                for (int node : comp) {
                    componentLabels[node] = compId;
                }
                compId++;
            }
        }

        Set<List<Integer>> condensationPairs = new TreeSet<>(Comparator.comparingInt((List<Integer> a) -> a.get(0)).thenComparingInt(a -> a.get(1)));

        for (int[] e : edges) {
            int uComp = componentLabels[e[0]];
            int vComp = componentLabels[e[1]];
            if (uComp != vComp) {
                condensationPairs.add(Arrays.asList(uComp, vComp));
            }
        }

        return Map.of(
                "component", toListInt(componentLabels),
                "condensation", new ArrayList<>(condensationPairs)
        );
    }

    private static void sccDfs1(int u, List<List<Integer>> adj, boolean[] visited, Deque<Integer> stack) {
        visited[u] = true;
        for (int v : adj.get(u)) {
            if (!visited[v]) {
                sccDfs1(v, adj, visited, stack);
            }
        }
        stack.push(u);
    }

    private static void sccDfs2(int u, List<List<Integer>> revAdj, boolean[] visited, List<Integer> comp) {
        visited[u] = true;
        comp.add(u);
        for (int v : revAdj.get(u)) {
            if (!visited[v]) {
                sccDfs2(v, revAdj, visited, comp);
            }
        }
    }

    static Map<String, Object> topo(Map<String, Object> input) {
        int n = Input.vertexCount(input);
        int[][] edges = Input.edges(input);

        List<List<Integer>> adj = new ArrayList<>();
        for (int i = 0; i < n; i++) adj.add(new ArrayList<>());
        for (int[] e : edges) adj.get(e[0]).add(e[1]);

        int[] state = new int[n]; // 0: unvisited, 1: visiting, 2: visited
        List<Integer> order = new ArrayList<>();

        for (int i = 0; i < n; i++) {
            if (state[i] == 0) {
                if (topoDfs(i, adj, state, order)) {
                    return Map.of("acyclic", false, "order", Collections.emptyList());
                }
            }
        }

        Collections.reverse(order);
        return Map.of("acyclic", true, "order", order);
    }

    private static boolean topoDfs(int u, List<List<Integer>> adj, int[] state, List<Integer> order) {
        state[u] = 1;
        for (int v : adj.get(u)) {
            if (state[v] == 1) return true;
            if (state[v] == 0) {
                if (topoDfs(v, adj, state, order)) return true;
            }
        }
        state[u] = 2;
        order.add(u);
        return false;
    }

    static Map<String, Object> dag(Map<String, Object> input) {
        int n = Input.vertexCount(input);
        int source = Input.source(input);
        int[][] edges = Input.edges(input);

        List<List<EdgeReference>> adj = new ArrayList<>();
        for (int i = 0; i < n; i++) adj.add(new ArrayList<>());
        for (int i = 0; i < edges.length; i++) {
            adj.get(edges[i][0]).add(new EdgeReference(edges[i][1], edges[i][2], i));
        }

        int[] state = new int[n];
        List<Integer> topoOrder = new ArrayList<>();

        
        for (int i = 0; i < n; i++) {
            if (state[i] == 0) {
                if (dagDfs(i, adj, state, topoOrder)) {
                    return Map.of(
                            "acyclic", false,
                            "distance", Collections.emptyList(),
                            "parent_edge", Collections.emptyList()
                    );
                }
            }
        }
        Collections.reverse(topoOrder);

        Long[] dist = new Long[n];
        int[] parentEdge = new int[n];
        Arrays.fill(parentEdge, -1);
        dist[source] = 0L;

        for (int u : topoOrder) {
            if (dist[u] != null) {
                for (EdgeReference edge : adj.get(u)) {
                    long newDist = dist[u] + edge.weight;
                    if (dist[edge.to] == null || newDist < dist[edge.to]) {
                        dist[edge.to] = newDist;
                        parentEdge[edge.to] = edge.edgeId;
                    }
                }
            }
        }

        List<Object> distList = new ArrayList<>();
        List<Integer> parentList = new ArrayList<>();
        for (int i = 0; i < n; i++) {
            distList.add(dist[i]);
            parentList.add(parentEdge[i]);
        }

        return Map.of(
                "acyclic", true,
                "distance", distList,
                "parent_edge", parentList
        );
    }

    private static boolean dagDfs(int u, List<List<EdgeReference>> adj, int[] state, List<Integer> order) {
        state[u] = 1;
        for (EdgeReference edge : adj.get(u)) {
            int v = edge.to;
            if (state[v] == 1) return true;
            if (state[v] == 0) {
                if (dagDfs(v, adj, state, order)) return true;
            }
        }
        state[u] = 2;
        order.add(u);
        return false;
    }

    private static List<Integer> toListInt(int[] arr) {
        List<Integer> list = new ArrayList<>(arr.length);
        for (int val : arr) list.add(val);
        return list;
    }

    private static final class EdgeInfo {
        int to, weight, edgeId;
        EdgeInfo(int to, int weight, int edgeId) {
            this.to = to;
            this.weight = weight;
            this.edgeId = edgeId;
        }
    }

    private static final class EdgeReference {
        int to, weight, edgeId;
        EdgeReference(int to, int weight, int edgeId) {
            this.to = to;
            this.weight = weight;
            this.edgeId = edgeId;
        }
    }

    private static final class DisjointSet {
        private final int[] parent;
        private final int[] size;
        private int componentCount;
        private int maxComponentSize;

        public DisjointSet(int n) {
            this.parent = new int[n];
            this.size = new int[n];
            this.componentCount = n;
            this.maxComponentSize = n > 0 ? 1 : 0;

            for (int i = 0; i < n; i++) {
                parent[i] = i;
                size[i] = 1;
            }
        }

        public int find(int i) {
            int root = i;
            while (root != parent[root]) {
                root = parent[root];
            }

            int current = i;
            while (current != root) {
                int next = parent[current];
                parent[current] = root;
                current = next;
            }
            return root;
        }

        public boolean union(int i, int j) {
            int rootI = find(i);
            int rootJ = find(j);

            if (rootI != rootJ) {
                if (size[rootI] < size[rootJ]) {
                    int temp = rootI;
                    rootI = rootJ;
                    rootJ = temp;
                }
                parent[rootJ] = rootI;
                size[rootI] += size[rootJ];
                maxComponentSize = Math.max(maxComponentSize, size[rootI]);
                componentCount--;
                return true;
            }
            return false;
        }

        public int getComponentCount() {
            return componentCount;
        }

        public int getMaxComponentSize() {
            return maxComponentSize;
        }

        public List<List<Integer>> getComponentSizes(int n) {
            Map<Integer, List<Integer>> map = new HashMap<>();
            for (int i = 0; i < n; i++) {
                int root = find(i);
                map.computeIfAbsent(root, k -> new ArrayList<>()).add(i);
            }
            List<List<Integer>> result = new ArrayList<>(map.values());
            result.sort((a, b) -> Integer.compare(b.size(), a.size()));
            return result;
        }
    }
}