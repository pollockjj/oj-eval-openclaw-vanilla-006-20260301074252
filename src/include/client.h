#ifndef CLIENT_H
#define CLIENT_H

#include <algorithm>
#include <cmath>
#include <iostream>
#include <limits>
#include <numeric>
#include <set>
#include <unordered_map>
#include <utility>
#include <vector>

extern int rows;
extern int columns;
extern int total_mines;

void Execute(int r, int c, int type);

namespace client_impl {

const int kDr[8] = {-1, -1, -1, 0, 0, 1, 1, 1};
const int kDc[8] = {-1, 0, 1, -1, 1, -1, 0, 1};

struct Constraint {
  std::vector<int> cells;
  int mines = 0;
};

struct Action {
  int r = -1;
  int c = -1;
  int type = 0;
  bool valid = false;
};

std::vector<std::string> known_map;

inline bool InBounds(int r, int c) {
  return r >= 0 && r < rows && c >= 0 && c < columns;
}

inline int Id(int r, int c) {
  return r * columns + c;
}

inline std::pair<int, int> Pos(int id) {
  return {id / columns, id % columns};
}

inline bool IsNumber(char ch) {
  return ch >= '0' && ch <= '8';
}

int UnknownNeighborCount(int r, int c) {
  int cnt = 0;
  for (int d = 0; d < 8; ++d) {
    const int nr = r + kDr[d];
    const int nc = c + kDc[d];
    if (InBounds(nr, nc) && known_map[nr][nc] == '?') {
      ++cnt;
    }
  }
  return cnt;
}

bool IsSubset(const std::vector<int> &a, const std::vector<int> &b) {
  if (a.size() > b.size()) {
    return false;
  }
  return std::includes(b.begin(), b.end(), a.begin(), a.end());
}

void ApplySubsetRule(const Constraint &small, const Constraint &large, std::set<int> &forced_safe,
                     std::set<int> &forced_mines) {
  if (!IsSubset(small.cells, large.cells)) {
    return;
  }

  std::vector<int> diff;
  diff.reserve(large.cells.size());
  std::set_difference(large.cells.begin(), large.cells.end(), small.cells.begin(), small.cells.end(),
                      std::back_inserter(diff));

  if (diff.empty()) {
    return;
  }

  const int mine_diff = large.mines - small.mines;
  if (mine_diff < 0 || mine_diff > static_cast<int>(diff.size())) {
    return;
  }
  if (mine_diff == 0) {
    forced_safe.insert(diff.begin(), diff.end());
  }
  if (mine_diff == static_cast<int>(diff.size())) {
    forced_mines.insert(diff.begin(), diff.end());
  }
}

void EnumerateComponent(const std::vector<int> &component_cells, const std::vector<int> &component_constraints,
                        const std::vector<Constraint> &constraints, std::set<int> &forced_safe,
                        std::set<int> &forced_mines, std::vector<double> &mine_probability) {
  const int n = static_cast<int>(component_cells.size());
  if (n == 0 || n > 18) {
    return;
  }

  std::unordered_map<int, int> local_index;
  local_index.reserve(component_cells.size() * 2);
  for (int i = 0; i < n; ++i) {
    local_index[component_cells[i]] = i;
  }

  const int m = static_cast<int>(component_constraints.size());
  std::vector<std::vector<int>> constraint_vars(m);
  std::vector<int> target(m, 0);

  for (int i = 0; i < m; ++i) {
    const Constraint &con = constraints[component_constraints[i]];
    target[i] = con.mines;
    constraint_vars[i].reserve(con.cells.size());
    for (int id : con.cells) {
      constraint_vars[i].push_back(local_index[id]);
    }
  }

  std::vector<std::vector<int>> var_to_constraints(n);
  for (int i = 0; i < m; ++i) {
    for (int v : constraint_vars[i]) {
      var_to_constraints[v].push_back(i);
    }
  }

  std::vector<int> order(n);
  std::iota(order.begin(), order.end(), 0);
  std::sort(order.begin(), order.end(), [&](int lhs, int rhs) {
    return var_to_constraints[lhs].size() > var_to_constraints[rhs].size();
  });

  std::vector<int> assigned(n, 0);
  std::vector<int> assigned_mines(m, 0);
  std::vector<int> unassigned(m, 0);
  for (int i = 0; i < m; ++i) {
    unassigned[i] = static_cast<int>(constraint_vars[i].size());
  }

  unsigned long long solution_count = 0;
  std::vector<unsigned long long> mine_count(n, 0);

  auto dfs = [&](auto &&self, int idx) -> void {
    if (idx == n) {
      for (int i = 0; i < m; ++i) {
        if (assigned_mines[i] != target[i]) {
          return;
        }
      }
      ++solution_count;
      for (int v = 0; v < n; ++v) {
        mine_count[v] += static_cast<unsigned long long>(assigned[v]);
      }
      return;
    }

    const int var = order[idx];
    for (int val = 0; val <= 1; ++val) {
      bool ok = true;
      assigned[var] = val;
      for (int con_idx : var_to_constraints[var]) {
        assigned_mines[con_idx] += val;
        --unassigned[con_idx];
        if (assigned_mines[con_idx] > target[con_idx] ||
            assigned_mines[con_idx] + unassigned[con_idx] < target[con_idx]) {
          ok = false;
        }
      }

      if (ok) {
        self(self, idx + 1);
      }

      for (int con_idx : var_to_constraints[var]) {
        ++unassigned[con_idx];
        assigned_mines[con_idx] -= val;
      }
    }
  };

  dfs(dfs, 0);

  if (solution_count == 0) {
    return;
  }

  for (int local_var = 0; local_var < n; ++local_var) {
    const int global_id = component_cells[local_var];
    mine_probability[global_id] =
        static_cast<double>(mine_count[local_var]) / static_cast<double>(solution_count);
    if (mine_count[local_var] == 0ULL) {
      forced_safe.insert(global_id);
    }
    if (mine_count[local_var] == solution_count) {
      forced_mines.insert(global_id);
    }
  }
}

Action BuildDecision() {
  Action action;
  const int total_cells = rows * columns;

  std::vector<Constraint> constraints;
  constraints.reserve(total_cells);

  std::set<int> forced_safe;
  std::set<int> forced_mines;
  std::vector<std::pair<int, int>> auto_candidates;

  int flagged_count = 0;
  int unknown_count = 0;

  for (int r = 0; r < rows; ++r) {
    for (int c = 0; c < columns; ++c) {
      if (known_map[r][c] == '@') {
        ++flagged_count;
      } else if (known_map[r][c] == '?') {
        ++unknown_count;
      }
    }
  }

  for (int r = 0; r < rows; ++r) {
    for (int c = 0; c < columns; ++c) {
      if (!IsNumber(known_map[r][c])) {
        continue;
      }

      const int number = known_map[r][c] - '0';
      int marked_neighbors = 0;
      std::vector<int> unknown_neighbors;
      unknown_neighbors.reserve(8);

      for (int d = 0; d < 8; ++d) {
        const int nr = r + kDr[d];
        const int nc = c + kDc[d];
        if (!InBounds(nr, nc)) {
          continue;
        }
        if (known_map[nr][nc] == '@') {
          ++marked_neighbors;
        } else if (known_map[nr][nc] == '?') {
          unknown_neighbors.push_back(Id(nr, nc));
        }
      }

      if (marked_neighbors == number && !unknown_neighbors.empty()) {
        auto_candidates.push_back({r, c});
      }

      if (unknown_neighbors.empty()) {
        continue;
      }

      std::sort(unknown_neighbors.begin(), unknown_neighbors.end());
      unknown_neighbors.erase(std::unique(unknown_neighbors.begin(), unknown_neighbors.end()), unknown_neighbors.end());

      const int mines_left = number - marked_neighbors;
      if (mines_left < 0 || mines_left > static_cast<int>(unknown_neighbors.size())) {
        continue;
      }

      Constraint con;
      con.cells = std::move(unknown_neighbors);
      con.mines = mines_left;
      constraints.push_back(std::move(con));
    }
  }

  for (const Constraint &con : constraints) {
    if (con.mines == 0) {
      forced_safe.insert(con.cells.begin(), con.cells.end());
    }
    if (con.mines == static_cast<int>(con.cells.size())) {
      forced_mines.insert(con.cells.begin(), con.cells.end());
    }
  }

  for (int i = 0; i < static_cast<int>(constraints.size()); ++i) {
    for (int j = i + 1; j < static_cast<int>(constraints.size()); ++j) {
      ApplySubsetRule(constraints[i], constraints[j], forced_safe, forced_mines);
      ApplySubsetRule(constraints[j], constraints[i], forced_safe, forced_mines);
    }
  }

  std::vector<std::vector<int>> cell_to_constraints(total_cells);
  for (int i = 0; i < static_cast<int>(constraints.size()); ++i) {
    for (int id : constraints[i].cells) {
      cell_to_constraints[id].push_back(i);
    }
  }

  std::vector<double> mine_probability(total_cells, -1.0);
  std::vector<char> visited_cell(total_cells, 0);
  std::vector<char> visited_constraint(constraints.size(), 0);

  for (int id = 0; id < total_cells; ++id) {
    if (cell_to_constraints[id].empty() || visited_cell[id]) {
      continue;
    }

    std::vector<int> component_cells;
    std::vector<int> component_constraints;
    std::vector<int> queue;
    queue.push_back(id);
    visited_cell[id] = 1;

    for (int head = 0; head < static_cast<int>(queue.size()); ++head) {
      const int cur_cell = queue[head];
      component_cells.push_back(cur_cell);

      for (int con_idx : cell_to_constraints[cur_cell]) {
        if (!visited_constraint[con_idx]) {
          visited_constraint[con_idx] = 1;
          component_constraints.push_back(con_idx);
        }
        for (int nxt_cell : constraints[con_idx].cells) {
          if (!visited_cell[nxt_cell]) {
            visited_cell[nxt_cell] = 1;
            queue.push_back(nxt_cell);
          }
        }
      }
    }

    EnumerateComponent(component_cells, component_constraints, constraints, forced_safe, forced_mines, mine_probability);
  }

  for (int id : forced_mines) {
    const auto [r, c] = Pos(id);
    if (known_map[r][c] == '?') {
      action = {r, c, 1, true};
      break;
    }
  }

  if (!action.valid) {
    std::sort(auto_candidates.begin(), auto_candidates.end());
    for (const auto &cell : auto_candidates) {
      int r = cell.first;
      int c = cell.second;
      if (!IsNumber(known_map[r][c])) {
        continue;
      }
      const int target = known_map[r][c] - '0';
      int marked = 0;
      int unknown = 0;
      for (int d = 0; d < 8; ++d) {
        const int nr = r + kDr[d];
        const int nc = c + kDc[d];
        if (!InBounds(nr, nc)) {
          continue;
        }
        if (known_map[nr][nc] == '@') {
          ++marked;
        } else if (known_map[nr][nc] == '?') {
          ++unknown;
        }
      }
      if (unknown > 0 && marked == target) {
        action = {r, c, 2, true};
        break;
      }
    }
  }

  if (!action.valid) {
    for (int id : forced_safe) {
      const auto [r, c] = Pos(id);
      if (known_map[r][c] == '?') {
        action = {r, c, 0, true};
        break;
      }
    }
  }

  if (action.valid) {
    return action;
  }

  std::vector<double> local_risk(total_cells, -1.0);
  for (const Constraint &con : constraints) {
    if (con.cells.empty()) {
      continue;
    }
    const double ratio = static_cast<double>(con.mines) / static_cast<double>(con.cells.size());
    for (int id : con.cells) {
      local_risk[id] = std::max(local_risk[id], ratio);
    }
  }

  double global_risk = 0.5;
  if (unknown_count > 0) {
    int mines_left = total_mines - flagged_count;
    mines_left = std::max(0, std::min(mines_left, unknown_count));
    global_risk = static_cast<double>(mines_left) / static_cast<double>(unknown_count);
  }

  int best_id = -1;
  double best_prob = std::numeric_limits<double>::infinity();
  int best_info = -1;

  for (int r = 0; r < rows; ++r) {
    for (int c = 0; c < columns; ++c) {
      if (known_map[r][c] != '?') {
        continue;
      }
      const int id = Id(r, c);
      double p = global_risk;
      if (mine_probability[id] >= 0.0) {
        p = mine_probability[id];
      } else if (local_risk[id] >= 0.0) {
        p = 0.5 * local_risk[id] + 0.5 * global_risk;
      }

      const int info = UnknownNeighborCount(r, c);
      const bool better_prob = (p + 1e-12 < best_prob);
      const bool same_prob = std::fabs(p - best_prob) <= 1e-12;
      const bool better_info = info > best_info;
      const bool better_id = best_id == -1 || id < best_id;

      if (better_prob || (same_prob && (better_info || (info == best_info && better_id)))) {
        best_prob = p;
        best_info = info;
        best_id = id;
      }
    }
  }

  if (best_id != -1) {
    const auto [r, c] = Pos(best_id);
    return {r, c, 0, true};
  }

  return {0, 0, 0, true};
}

}  // namespace client_impl

void InitGame() {
  client_impl::known_map.assign(rows, std::string(columns, '?'));

  int first_row, first_column;
  std::cin >> first_row >> first_column;
  Execute(first_row, first_column, 0);
}

void ReadMap() {
  client_impl::known_map.assign(rows, std::string(columns, '?'));
  for (int r = 0; r < rows; ++r) {
    std::cin >> client_impl::known_map[r];
  }
}

void Decide() {
  const client_impl::Action action = client_impl::BuildDecision();
  Execute(action.r, action.c, action.type);
}

#endif
