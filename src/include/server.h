#ifndef SERVER_H
#define SERVER_H

#include <cstdlib>
#include <iostream>
#include <queue>
#include <string>
#include <vector>

int rows;
int columns;
int total_mines;
int game_state;

namespace server_impl {

constexpr int kHidden = 0;
constexpr int kVisited = 1;
constexpr int kMarked = 2;

const int kDr[8] = {-1, -1, -1, 0, 0, 1, 1, 1};
const int kDc[8] = {-1, 0, 1, -1, 1, -1, 0, 1};

std::vector<std::string> board;
std::vector<std::vector<int>> adjacent_mines;
std::vector<std::vector<int>> cell_state;

int visited_safe_count = 0;
int correctly_marked_mine_count = 0;

bool InBounds(int r, int c) {
  return r >= 0 && r < rows && c >= 0 && c < columns;
}

void RecomputeGameState() {
  if (game_state == -1) {
    return;
  }
  const int safe_cells = rows * columns - total_mines;
  game_state = (visited_safe_count == safe_cells) ? 1 : 0;
}

void VisitConnectedSafeRegion(int r, int c) {
  if (!InBounds(r, c) || cell_state[r][c] != kHidden || board[r][c] == 'X') {
    return;
  }

  std::queue<std::pair<int, int>> q;
  cell_state[r][c] = kVisited;
  ++visited_safe_count;
  if (adjacent_mines[r][c] == 0) {
    q.push({r, c});
  }

  while (!q.empty()) {
    const auto [cr, cc] = q.front();
    q.pop();
    for (int d = 0; d < 8; ++d) {
      const int nr = cr + kDr[d];
      const int nc = cc + kDc[d];
      if (!InBounds(nr, nc) || cell_state[nr][nc] != kHidden || board[nr][nc] == 'X') {
        continue;
      }
      cell_state[nr][nc] = kVisited;
      ++visited_safe_count;
      if (adjacent_mines[nr][nc] == 0) {
        q.push({nr, nc});
      }
    }
  }
}

}  // namespace server_impl

void InitMap() {
  std::cin >> rows >> columns;
  server_impl::board.assign(rows, std::string(columns, '.'));
  server_impl::adjacent_mines.assign(rows, std::vector<int>(columns, 0));
  server_impl::cell_state.assign(rows, std::vector<int>(columns, server_impl::kHidden));

  total_mines = 0;
  game_state = 0;
  server_impl::visited_safe_count = 0;
  server_impl::correctly_marked_mine_count = 0;

  for (int r = 0; r < rows; ++r) {
    std::cin >> server_impl::board[r];
    for (int c = 0; c < columns; ++c) {
      if (server_impl::board[r][c] == 'X') {
        ++total_mines;
      }
    }
  }

  for (int r = 0; r < rows; ++r) {
    for (int c = 0; c < columns; ++c) {
      if (server_impl::board[r][c] == 'X') {
        continue;
      }
      int cnt = 0;
      for (int d = 0; d < 8; ++d) {
        const int nr = r + server_impl::kDr[d];
        const int nc = c + server_impl::kDc[d];
        if (server_impl::InBounds(nr, nc) && server_impl::board[nr][nc] == 'X') {
          ++cnt;
        }
      }
      server_impl::adjacent_mines[r][c] = cnt;
    }
  }
}

void VisitBlock(int r, int c) {
  if (!server_impl::InBounds(r, c) || game_state != 0) {
    return;
  }
  if (server_impl::cell_state[r][c] == server_impl::kVisited ||
      server_impl::cell_state[r][c] == server_impl::kMarked) {
    return;
  }

  if (server_impl::board[r][c] == 'X') {
    server_impl::cell_state[r][c] = server_impl::kVisited;
    game_state = -1;
    return;
  }

  server_impl::VisitConnectedSafeRegion(r, c);
  server_impl::RecomputeGameState();
}

void MarkMine(int r, int c) {
  if (!server_impl::InBounds(r, c) || game_state != 0) {
    return;
  }
  if (server_impl::cell_state[r][c] == server_impl::kVisited ||
      server_impl::cell_state[r][c] == server_impl::kMarked) {
    return;
  }

  server_impl::cell_state[r][c] = server_impl::kMarked;
  if (server_impl::board[r][c] == 'X') {
    ++server_impl::correctly_marked_mine_count;
    server_impl::RecomputeGameState();
    return;
  }

  game_state = -1;
}

void AutoExplore(int r, int c) {
  if (!server_impl::InBounds(r, c) || game_state != 0) {
    return;
  }
  if (server_impl::cell_state[r][c] != server_impl::kVisited || server_impl::board[r][c] == 'X') {
    return;
  }

  const int target_mines = server_impl::adjacent_mines[r][c];
  int marked = 0;
  for (int d = 0; d < 8; ++d) {
    const int nr = r + server_impl::kDr[d];
    const int nc = c + server_impl::kDc[d];
    if (server_impl::InBounds(nr, nc) &&
        server_impl::cell_state[nr][nc] == server_impl::kMarked) {
      ++marked;
    }
  }

  if (marked != target_mines) {
    return;
  }

  for (int d = 0; d < 8; ++d) {
    const int nr = r + server_impl::kDr[d];
    const int nc = c + server_impl::kDc[d];
    if (!server_impl::InBounds(nr, nc) ||
        server_impl::cell_state[nr][nc] != server_impl::kHidden ||
        server_impl::board[nr][nc] == 'X') {
      continue;
    }
    server_impl::VisitConnectedSafeRegion(nr, nc);
  }

  server_impl::RecomputeGameState();
}

void ExitGame() {
  if (game_state == 1) {
    std::cout << "YOU WIN!" << std::endl;
    std::cout << server_impl::visited_safe_count << " " << total_mines << std::endl;
  } else {
    std::cout << "GAME OVER!" << std::endl;
    std::cout << server_impl::visited_safe_count << " " << server_impl::correctly_marked_mine_count << std::endl;
  }
  exit(0);
}

void PrintMap() {
  for (int r = 0; r < rows; ++r) {
    for (int c = 0; c < columns; ++c) {
      char out = '?';
      if (game_state == 1 && server_impl::board[r][c] == 'X') {
        out = '@';
      } else if (server_impl::cell_state[r][c] == server_impl::kHidden) {
        out = '?';
      } else if (server_impl::cell_state[r][c] == server_impl::kVisited) {
        if (server_impl::board[r][c] == 'X') {
          out = 'X';
        } else {
          out = static_cast<char>('0' + server_impl::adjacent_mines[r][c]);
        }
      } else if (server_impl::cell_state[r][c] == server_impl::kMarked) {
        out = (server_impl::board[r][c] == 'X') ? '@' : 'X';
      }
      std::cout << out;
    }
    std::cout << std::endl;
  }
}

#endif
