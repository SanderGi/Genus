import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintStream;
import java.util.*;

public class BalabanRandomAdjCycle {
    public static void main(String[] args) throws FileNotFoundException {
        File outputFile = new File("BalabanOutput.txt");
        PrintStream output = new PrintStream(outputFile);
        boolean found = false;
        for (int i = 0; i < 1; i++) {
            // randomize(); // GET RID OF FOR NON RANDOM CALL
            int[][] test = new int[70][3];
            File myFile = new File("19CycleAdjList.txt");
            Scanner fileScan = new Scanner(myFile);
            int line = 0;
            while (fileScan.hasNextLine()) {
                String currentLine = fileScan.nextLine();
                Scanner lineScan = new Scanner(currentLine);
                test[line][0] = Integer.parseInt(lineScan.next());
                test[line][1] = Integer.parseInt(lineScan.next());
                test[line][2] = Integer.parseInt(lineScan.next());
                line++;
            }
            Set<int[]> edges = getEdges(test);
            int startPrevRow = 0;
            int startRow = 0;

            List<Cycle> cycles = new ArrayList<>();
            for (int[] curr : edges) {
                List<String> pairs = new ArrayList<>();
                startPrevRow = curr[0];
                startRow = curr[1];
                findPath(test, startPrevRow, startRow, pairs);
                Cycle currCycle = new Cycle(pairs);
                cycles.add(currCycle);
            }
            removeDuplicates(cycles);
            if (cycles.size() > 12) {
                writeCycles(cycles, output);
                found = true;
            }
        }
        if (!found) {
            output.println("No cycles over 12 found.");
        }
    }

    public static void writeCycles(List<Cycle> cycles, PrintStream output) {
        output.println(cycles.size() + " Cycles created");
        for (int i = 0; i < cycles.size(); i++) {
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
        for (int i = 0; i < test.length; i++) {
            edges.add(new int[] { test[i][0], i + 1 });
            edges.add(new int[] { test[i][1], i + 1 });
            edges.add(new int[] { test[i][2], i + 1 });
        }
        return edges;
    }

    public static void findPath(int[][] test, int startPrevRow, int startR, List<String> pairs)
            throws FileNotFoundException {
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

    public static void randomize() throws FileNotFoundException {
        int[][] inputData = {
                { 3, 19, 21 }, { 20, 4, 23 }, { 5, 1, 24 }, { 2, 6, 26 }, { 7, 3, 27 },
                { 4, 8, 29 }, { 30, 5, 9 }, { 6, 32, 10 }, { 7, 33, 11 }, { 35, 12, 8 },
                { 13, 9, 36 }, { 10, 38, 14 }, { 39, 11, 15 }, { 16, 12, 41 }, { 13, 17, 42 },
                { 44, 14, 18 }, { 19, 45, 15 }, { 47, 20, 16 }, { 1, 17, 48 }, { 50, 2, 18 },
                { 22, 51, 1 }, { 37, 21, 23 }, { 2, 52, 22 }, { 53, 25, 3 }, { 24, 26, 40 },
                { 25, 4, 54 }, { 55, 5, 28 }, { 29, 43, 27 }, { 6, 28, 56 }, { 31, 7, 57 },
                { 46, 30, 32 }, { 8, 58, 31 }, { 9, 34, 59 }, { 33, 49, 35 }, { 60, 10, 34 },
                { 37, 61, 11 }, { 38, 36, 22 }, { 12, 37, 62 }, { 40, 63, 13 }, { 41, 25, 39 },
                { 14, 40, 64 }, { 15, 43, 65 }, { 28, 44, 42 }, { 43, 16, 66 }, { 17, 46, 67 },
                { 45, 31, 47 }, { 46, 18, 68 }, { 19, 69, 49 }, { 34, 50, 48 }, { 70, 20, 49 },
                { 66, 58, 21 }, { 23, 65, 57 }, { 68, 60, 24 }, { 26, 59, 67 }, { 70, 27, 62 },
                { 69, 29, 61 }, { 30, 52, 64 }, { 32, 63, 51 }, { 66, 33, 54 }, { 53, 35, 65 },
                { 36, 68, 56 }, { 55, 67, 38 }, { 58, 70, 39 }, { 57, 69, 41 }, { 52, 60, 42 },
                { 44, 51, 59 }, { 62, 45, 54 }, { 61, 53, 47 }, { 48, 64, 56 }, { 63, 50, 55 }
        };

        // Initialize Random object
        Random random = new Random();

        // Process each row
        for (int[] row : inputData) {
            // Randomly rearrange the entries in the row
            for (int i = row.length - 1; i > 0; i--) {
                int j = random.nextInt(i + 1);
                // Swap row[i] with row[j]
                int temp = row[i];
                row[i] = row[j];
                row[j] = temp;
            }
        }
        File newFile = new File("C:\\Users\\austi\\OneDrive\\Documents\\cyclecode\\BalabanAdjList.txt");
        PrintStream newPrint = new PrintStream(newFile);
        // Print the new output data
        for (int[] row : inputData) {
            newPrint.println(Arrays.toString(row).replaceAll("[\\[\\],]", ""));
        }
    }
}
