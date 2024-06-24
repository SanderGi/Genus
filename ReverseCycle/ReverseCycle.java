package ReverseCycle;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Scanner;
import java.util.Set;
import java.io.PrintWriter;

/**
 * ReverseCycle
 */
public class ReverseCycle {
    private static final String FILENAME = "output1.txt"; // change this to the input with cycles
    private static final String OUTPUT_FILENAME = "adjacencylist.txt"; // change this to the output file
    private static final int STARTS_AT = 0; // change this if the vertices start at a different number
    
    private static final int NUM_VERTICES = 70; // this is fixed

    public static void main(String[] args) {
        List<Set<Integer>> adjacencyList = new ArrayList<>(NUM_VERTICES);
        for (int i = 0; i < NUM_VERTICES; i++) {
            adjacencyList.add(new LinkedHashSet<>());
        }

        File file = new File(FILENAME);
        try {
            Scanner scanner = new Scanner(file);

            // first line has the number of cycles as the first integer
            String line = scanner.nextLine();
            int cycles = Integer.parseInt(line.split(" ")[0]);
            System.out.println("Number of cycles: " + cycles);

            for (int cycle = 0; cycle < cycles; cycle++) {
                // first line is just the cycle number
                scanner.nextLine();

                // read the number of elements in the cycle
                line = scanner.nextLine();
                int n = Integer.parseInt(line.split(": ")[1]);
                System.out.println("Number of elements in cycle " + (cycle + 1) + ": " + n);

                // read the cycle
                int[][] cycleEdges = new int[n][2];
                for (int i = 0; i < n; i++) {
                    line = scanner.nextLine();
                    String[] vertices = line.split(", ");
                    cycleEdges[i][0] = Integer.parseInt(vertices[0]) + 1 - STARTS_AT;
                    cycleEdges[i][1] = Integer.parseInt(vertices[1]) + 1 - STARTS_AT;
                }
                int u = cycleEdges[n - 1][0];
                int v = cycleEdges[n - 1][1];
                adjacencyList.get(v - 1).add(u);
                for (int i = 0; i < n; i++) {
                    u = cycleEdges[i][0];
                    v = cycleEdges[i][1];
                    adjacencyList.get(u - 1).add(v);
                    adjacencyList.get(v - 1).add(u);
                }

                // skip 2 blank lines
                if (scanner.hasNextLine()) scanner.nextLine();
                if (scanner.hasNextLine()) scanner.nextLine();
            }

            scanner.close();
        } catch (FileNotFoundException e) {
            System.err.println("Could not find file " + FILENAME);
        }

        // print the adjacency list
        for (int i = 0; i < NUM_VERTICES; i++) {
            List<Integer> row = new ArrayList<>(adjacencyList.get(i));
            for (int j = 0; j < adjacencyList.get(i).size(); j++) {
                System.out.print(row.get(j) - 1 + STARTS_AT + " ");
            }
            System.out.println();
        }

        // save the adjacency list to a file
        try {
            File output = new File(OUTPUT_FILENAME);
            PrintWriter writer = new PrintWriter(output);

            for (int i = 0; i < NUM_VERTICES; i++) {
                List<Integer> row = new ArrayList<>(adjacencyList.get(i));
                for (int j = 0; j < adjacencyList.get(i).size(); j++) {
                    writer.print(row.get(j) - 1 + STARTS_AT + " ");
                }
                writer.println();
            }

            writer.close();
        } catch (FileNotFoundException e) {
            System.err.println("Could not write to file " + OUTPUT_FILENAME);
        }
    }
}
