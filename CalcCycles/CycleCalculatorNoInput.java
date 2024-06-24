import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintStream;
import java.util.*;

public class CycleCalculatorNoInput {
    public static void main(String[] args) throws FileNotFoundException {
        // setting minimum number of cycles to print
        int minCycles = 16;
        System.out.println("Minimum number of cycles to print: " + minCycles);
        // filling freeLines List with user inputted lines
        List<Integer> nonFreeLines = Arrays.asList(new Integer[] {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21, 22, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 43, 44, 50, 51, 56, 58, 61, 63, 66});
        List<Integer> freeLines = new ArrayList<>();
        for (int i = 1; i <= 70; i++) {
            if (!nonFreeLines.contains(i)) {
                freeLines.add(i);
            }
        }
        System.out.println("Free lines: " + freeLines);
        // instantiating Scanner fileScan and printStream outPut.
        File myFile = new File("William2OutputAdj.txt");
        Scanner fileScan = new Scanner(myFile); // arrays line scan
        File outputFile = new File("CycleCalculatorOutput.txt");
        PrintStream output = new PrintStream(outputFile);// output scan
        // creating int[][] adjList from adjList.txt
        int numRows = 0;
        while (fileScan.hasNextLine()) {
            fileScan.nextLine();
            numRows++;
        }
        int[][] adjList = new int[numRows][3]; 
        // filling int[][] adjList from adjList.txt
        int currRow = 0;
        Scanner adjListScan = new Scanner(myFile);
        while (adjListScan.hasNextLine()) {
            String currentLine = adjListScan.nextLine();
            Scanner lineScan = new Scanner(currentLine);
            adjList[currRow][0] = Integer.parseInt(lineScan.next());
            adjList[currRow][1] = Integer.parseInt(lineScan.next());
            adjList[currRow][2] = Integer.parseInt(lineScan.next());
            currRow++;
        }
        // making sure all rows are ordered with col 1 < col 2.
        orderAdjList(adjList);
        // generate binary combinations
        generateBinaryCombinations(adjList, output, minCycles, freeLines);
        System.out.println("done.");
    }

    // runs through all possible combinations for the given free rows of the adjacency list, 
    // generating and printing the cycles for each combination to the output.txt file
    public static void generateBinaryCombinations(int[][] adjList, PrintStream output, int minCycles, List<Integer> freeLines) throws FileNotFoundException {
        int numFreeLines = freeLines.size();
        System.out.println("Number of Free lines: " + numFreeLines);
        // total combinations for binary Strings
        long totalCombinations = 1l << numFreeLines; // Total combinations is 2^numFreeLines
        System.out.println("Total Combinations: " + totalCombinations);
        // BINARY GENERATION LOOP STARTS
        for (int i = 0; i < totalCombinations; i++) {
            if (i % 100000 == 0) System.out.println("Iteration: " + i);
            String a = "";
            String binaryString = "";
            if (numFreeLines != 0) {
                // creating binary string
                a = Integer.toBinaryString(i);
                binaryString = String.format("%" + numFreeLines + "s", a).replace(' ', '0');
                // updating adjList based on chosen free lines and current binary generation
                for(int j = 0; j < freeLines.size(); j++) {
                    int currLine = freeLines.get(j) - 1;
                    int currInt = Integer.parseInt(binaryString.substring(j, j + 1));
                    // if binary string wants this line switched and it's not already or if binary string wants this line switched and it's not
                    if ((currInt == 1 && adjList[currLine][0] < adjList[currLine][1]) || currInt == 0 && adjList[currLine][0] > adjList[currLine][1]) {
                        // swaps index 0 and 1
                        int hold = adjList[currLine][1];
                        adjList[currLine][1] = adjList[currLine][0];
                        adjList[currLine][0] = hold;
                    }
                }
            }
            // generating set of all edges
            Set<int[]> edges = getEdges(adjList);
            // Iterating through every edge, finding path for it based on adjList, then add it to cycles List.
            int startPrevRow = 0;
            int startRow = 0;
            List<Cycle> cycles = new ArrayList<>();
            for(int[] curr: edges) {
                List<String> pairs = new ArrayList<>();
                startPrevRow = curr[0];
                startRow = curr[1];
                findPath(adjList, startPrevRow, startRow, pairs);
                Cycle currCycle = new Cycle(pairs);
                cycles.add(currCycle);
            }
            // removing duplicate cycles from cycles List
            removeDuplicates(cycles);
            // print cycles if over given int minCycles
            if (cycles.size() >= minCycles) {
                writeCycles(cycles, output);
            }
        } // BINARY GENERATION LOOP ENDS
    }

    // Orders every row of int[][] adjList so that the first number is less than the second without changing the order of numbers.
    public static void orderAdjList(int[][] adjList) {
        for(int i = 0; i < adjList.length; i++) {
            int colOne = adjList[i][0];
            int colTwo = adjList[i][1];
            int colThree = adjList[i][2];
            if (colOne > colTwo) { // if the cols need to be switched
                if (colThree > colOne) { // cycle left
                    adjList[i][0] = colTwo;
                    adjList[i][1] = colThree;
                    adjList[i][2] = colOne;
                } else { // cycle right
                    adjList[i][0] = colThree;
                    adjList[i][1] = colOne;
                    adjList[i][2] = colTwo;
                }
            }
        }
    }

    // prints out the int[][] adjList
    public static void printCurrentAdjList(int[][] adjList) {
        for(int i = 0; i < adjList.length; i++) {
            System.out.print(adjList[i][0] + " ");
            System.out.print(adjList[i][1] + " ");
            System.out.println(adjList[i][2]);
        }
        System.out.println();
    }

    // Prints cycles to output.txt
    public static void writeCycles(List<Cycle> cycles, PrintStream output) {
        output.println(cycles.size() + " Cycles:");
        for(int i = 0; i < cycles.size(); i++) {
            output.println("Cycle " + (i + 1) + ": ");
            output.println("Length: " + cycles.get(i).length);
            output.println(cycles.get(i));
            output.println();
        }
    }

    // removes the duplicate cycles from the given List.
    public static void removeDuplicates(List<Cycle> cycles) {
        for (int i = 0; i < cycles.size(); i++) {
            Cycle current = cycles.get(i);
            Iterator<Cycle> iterator = cycles.listIterator(i + 1);
            while (iterator.hasNext()) {
                Cycle next = iterator.next();
                if (current.compareTo(next) == 0) {
                    iterator.remove();
                }
            }
        }
    }

    // returns a set<int[]> of all edges made from the adjacency list. Each int[] is length 2 and the 
    // edge being line number -> value of each col of that row.
    public static Set<int[]> getEdges(int[][] adjList) {
        Set<int[]> edges = new HashSet<>();
        for(int i = 0; i < adjList.length; i++) {
            edges.add(new int[]{adjList[i][0], i + 1});
            edges.add(new int[]{adjList[i][1], i + 1});
            edges.add(new int[]{adjList[i][2], i + 1});
        }
        return edges;
    }

    // finds a cycle for the current edge.
    public static void findPath(int[][] adjList, int startPrevRow, int startR, List<String> pairs) {
        int startRow = -1;
        int prevRow = startPrevRow;
        int currRow = startR;
        int nextColIndex = -1;
        while (true) {
            if (startRow == currRow && startPrevRow == prevRow) {
                break;
            }
            startRow = startR;
            for (int i = 0; i < adjList[0].length; i++) {
                if (adjList[currRow - 1][i] == prevRow) {
                    if (i + 1 >= adjList[0].length) {
                        nextColIndex = 0;
                    } else {
                        nextColIndex = i + 1;
                    }
                    prevRow = currRow;
                    currRow = adjList[currRow - 1][nextColIndex];
                    pairs.add(prevRow + ", " + currRow);
                    break;
                }
            }
        }
    }
}
