import sys
from collections import deque
import logging

logging.basicConfig(filename='my.log', encoding='utf-8', level=logging.INFO)

def main():
    # Read input lines from stdin
    input_lines = sys.stdin.readlines()
    
    # print the input lines for debug
    # with open('log.txt', 'w') as log_file:
    #     for line in input_lines:
    #         log_file.write(line)

    # initialize maze: walls are 1, floor is 0, exit is any floor on the outside edge
    r_start, c_start = [int(c) for c in input_lines[0].split()]
    rows, cols = [int(c) for c in input_lines[1].split()]

    maze = [[0]*(cols) for _ in range(rows)]

    for i in range(2, len(input_lines), 2):
        x, y = int(input_lines[i]), int(input_lines[i+1])
        maze[y][x] = 1
    
    # print maze for debugging
    # with open('log.txt', 'w') as file:
    #     file.write(f"# rows: {rows}, # cols: {cols}\n")
    #     file.write(f"start: {r_start} {c_start}\n")
    #     for item in maze:
    #         file.write(f"{item}\n")


    # solve maze via BFS (iterative implementation)
    # propagate outwards from the start position
    # keep track of the path
    # the first arm to reach an exit is guaranteed to be the shortest path
    # never visit the same cell twice
    res = ""

    q = deque()
    visited = set()
    dir = [(-1, 0), (0, 1), (1, 0), (0, -1)]

    q.append([r_start, c_start, []])
    
    while q:
        r, c, p = q.popleft()

        # logging.info(f"RUN {r}, {c}, {p}")

        if (r, c) in visited:
            continue
        visited.add((r, c))

        # exit condition
        if (r == rows-1 or r == 0 or c == 0 or c == cols - 1) and maze[r][c] == 0:
            res = p + ["4"]
            break
        
        # propagations
        for i in range(len(dir)):
            dx, dy = dir[i][0], dir[i][1]

            # logging.info(f"CAND {r+dx}, {c+dy}, {p + [str(i)]}")

            if ( not (0 <= r + dx < rows) or
                 not (0 <= c + dy < cols) or
                 maze[r+dx][c+dy] == 1 or
                 (r+dx, c+dy) in visited):
                continue

            q.append([r+dx, c+dy, p + [str(i)]])

    # result printing for debug
    # with open('log.txt', 'w') as file:
    #     file.write(f"{res}\n")

    # on the case of no possible solution, return a "0"
    if not res: res = ["0"]

    # else, return the path and the maze is solved
    res = " ".join(res)
    sys.stdout.write(res + "\n")

if __name__ == "__main__":
    main()