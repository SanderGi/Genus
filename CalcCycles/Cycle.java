import java.util.*;
public class Cycle implements Comparable<Cycle> {
    public List<String> edges;
    public int length;

    public Cycle(List<String> edges) {
        this.edges = edges;
        this.length = edges.size();
    }

    public int compareTo(Cycle other) {
        if (other.edges.size() != edges.size()) {
            return -1;
        }
        
        int shift = -1;
        String curr = edges.get(0);
        
        // Find the shift value
        for (int i = 0; i < other.edges.size(); i++) {
            if (other.edges.get(i).equals(curr)) {
                shift = i;
                break;  // Break after finding the first occurrence
            }
        }
        
        if (shift == -1) {
            return -1;
        }
        
        // Check for equality by shifting
        for (int i = 0; i < edges.size(); i++) {
            int index = (shift + i) % edges.size();
            if (!other.edges.get(index).equals(edges.get(i))) {
                return -1;
            }
        }
        
        return 0;
    }

    public String toString() {
        String s = "";
        for (String curr: edges) {
            s += curr;
            s += "\n";
        }
        return s;
    }
    
}
