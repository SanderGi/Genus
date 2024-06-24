import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintStream;
import java.util.*;

public class CalulateCycles {
// Manually fill arrays.txt
// start binary loop
// update arrays.txt from binary    
// fill int[][] from arrays.txt
// generate cycles
// remove duplicate cycles
// print cycles
// repeat binary loop
    public static void main(String[] args) throws FileNotFoundException {
        int[][] test = new int[70][3]; 
        File myFile = new File("William2OutputAdj.txt");
        Scanner fileScan = new Scanner(myFile); // arrays line scan
        File outputFile = new File("calccyclesoutput.txt");
        PrintStream output = new PrintStream(outputFile);// output scan
        int line = 0;
        // filling int[][] test from arrays.txt
        while (fileScan.hasNextLine()) {
            String currentLine = fileScan.nextLine();
            Scanner lineScan = new Scanner(currentLine);
            test[line][0] = Integer.parseInt(lineScan.next());
            test[line][1] = Integer.parseInt(lineScan.next());
            test[line][2] = Integer.parseInt(lineScan.next());
            line++;
        }
        generateBinaryCombinations(27, test, output);               // CHANGE THIS FOR DIFFERENT NUMBER OF NON-FIXED ROWS
    }

    // Fills choices array
    public static void fillChoices(boolean[] choices, Scanner indexScanner) {
        int currentIndex = 0;
        while(indexScanner.hasNextLine()) {
            int choice = Integer.parseInt(indexScanner.nextLine());
            if (choice == 0) {
                choices[currentIndex] = false;
            } else {
                choices[currentIndex] = true;
            }
            currentIndex++;
        }
    }

    public static void generateBinaryCombinations(int n, int[][] test, PrintStream output) throws FileNotFoundException {
        File indexFile = new File("C:\\Users\\austi\\OneDrive\\Documents\\cyclecode\\indices.txt");
        Scanner indexScanner = new Scanner(indexFile);
        boolean[] choices = new boolean[70];
        fillChoices(choices, indexScanner);
            //  FILLING CHOICES ARRAY
        
  
            // BINARY GENERATION LOOP STARTS
        int totalCombinations = 1 << n; // Total combinations is 2^n
        for (int i = 0; i < totalCombinations; i++) { // iterating through binary strings
            String a = Integer.toBinaryString(i);
            String binaryString = String.format("%" + n + "s", a).replace(' ', '0');


            // FILLING binaries WITH THE CURRENT BINARY ITERATION
            int[] binaries = new int[binaryString.length()];
            for(int j = 0; j < binaryString.length(); j++) {
                binaries[j] = Integer.parseInt(binaryString.substring(j, j + 1));
            }


            // ex: choices = (t, f, f, t, f, f, f, t) -> size of the whole 2d array
            // ex: binaries = (1, 0, 1) -> only the size of the things we are changing

            // UPDATING test for the choices we made and the current binary 
            int binaryIndex = 0;
            for(int j = 0; j < test.length; j++) {
                if (choices[j]) { // if we want this row changed
                    if (binaries[binaryIndex] == 1) { // If current binary wants this row swaapped
                        if (test[j][0] < test[j][1]) { // If current row is not already swapped
                            int hold = test[j][1];
                            test[j][1] = test[j][0];    // swap index one and two
                            test[j][0] = hold;
                        }
                    }
                    binaryIndex++; // Update binaryIndex
                }
            }

            Set<int[]> edges = getEdges(test);
            int startPrevRow = 0;
            int startRow = 0;
            
            List<Cycle> cycles = new ArrayList<>();
            for(int[] curr: edges) {
                List<String> pairs = new ArrayList<>();
                startPrevRow = curr[0];
                startRow = curr[1];
                findPath(test, startPrevRow, startRow, pairs);
                Cycle currCycle = new Cycle(pairs);
                cycles.add(currCycle);
            }
            removeDuplicates(cycles);
            if (cycles.size() > 15) {    // CHANGE FOR PRINTING DIFF NUMBER OF CYCLES
                writeCycles(cycles, output);
            }
        } // BINARY GENERATION LOOP ENDS
    }

    public static void printChoices(boolean[] choices) {
        for(int i = 0; i < choices.length; i++) {
            if (choices[i] == true) {
                System.out.print("t ");
            } else {
                System.out.print("f ");
            }
        }
    }

    public static void printCurrentAdjList(int[][] test) {
        for(int i = 0; i < test.length; i++) {
            System.out.print(test[i][0] + " ");
            System.out.print(test[i][1] + " ");
            System.out.println(test[i][2]);
        }
    }

    public static void writeCycles(List<Cycle> cycles, PrintStream output) {
        output.println(cycles.size() + " Cycles:");
        for(int i = 0; i < cycles.size(); i++) {
            output.println("Cycle " + (i + 1) + ": ");
            output.println("Length: " + cycles.get(i).length);
            output.println(cycles.get(i));
            output.println();
        }
    }

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

    public static Set<int[]> getEdges(int[][] test) {
        Set<int[]> edges = new HashSet<>();
        for(int i = 0; i < test.length; i++) {
            edges.add(new int[]{test[i][0], i + 1});
            edges.add(new int[]{test[i][1], i + 1});
            edges.add(new int[]{test[i][2], i + 1});
        }
        return edges;
    }

    public static void findPath(int[][] test, int startPrevRow, int startR, List<String> pairs) throws FileNotFoundException {
        int startRow = -1;
        int prevRow = startPrevRow;
        int currRow = startR;
        int nextColIndex = -1;
        while (true) {
            if (startRow == currRow && startPrevRow == prevRow) {
                break;
            }
            startRow = startR;
            for (int i = 0; i < test[0].length; i++) {
                if (test[currRow - 1][i] == prevRow) {
                    if (i + 1 >= test[0].length) {
                        nextColIndex = 0;
                    } else {
                        nextColIndex = i + 1;
                    }
                    prevRow = currRow;
                    currRow = test[currRow - 1][nextColIndex];
                    pairs.add(prevRow + ", " + currRow);
                    break;
                }
            }
        }
    }
}
