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

struct EnumeratedComponentStats {
  std::vector<int> cells;
  std::vector<long double> ways_by_mines;
  std::vector<std::vector<long double>> cell_mine_ways_by_mines;
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

std::vector<long double> ConvolveLimited(const std::vector<long double> &lhs, const std::vector<long double> &rhs,
                                         int limit) {
  if (limit < 0 || lhs.empty() || rhs.empty()) {
    return {};
  }
  std::vector<long double> result(limit + 1, 0.0L);
  const int lhs_limit = std::min(limit, static_cast<int>(lhs.size()) - 1);
  const int rhs_limit = std::min(limit, static_cast<int>(rhs.size()) - 1);
  for (int i = 0; i <= lhs_limit; ++i) {
    if (lhs[i] == 0.0L) {
      continue;
    }
    const int max_j = std::min(rhs_limit, limit - i);
    for (int j = 0; j <= max_j; ++j) {
      if (rhs[j] == 0.0L) {
        continue;
      }
      result[i + j] += lhs[i] * rhs[j];
    }
  }
  return result;
}

std::vector<long double> BuildBinomialLimited(int n, int limit) {
  if (n < 0 || limit < 0) {
    return {};
  }
  std::vector<long double> choose(limit + 1, 0.0L);
  choose[0] = 1.0L;
  const int upto = std::min(n, limit);
  for (int k = 1; k <= upto; ++k) {
    choose[k] = choose[k - 1] * static_cast<long double>(n - k + 1) / static_cast<long double>(k);
  }
  return choose;
}

void ApplyGlobalMineConditioning(const std::vector<EnumeratedComponentStats> &components, int mines_remaining,
                                 int pool_cells, std::vector<double> &mine_probability, double &pool_risk) {
  const int component_count = static_cast<int>(components.size());
  if (component_count == 0 || mines_remaining < 0) {
    return;
  }

  std::vector<std::vector<long double>> prefix(component_count + 1);
  std::vector<std::vector<long double>> suffix(component_count + 1);
  prefix[0].assign(mines_remaining + 1, 0.0L);
  prefix[0][0] = 1.0L;
  for (int i = 0; i < component_count; ++i) {
    prefix[i + 1] = ConvolveLimited(prefix[i], components[i].ways_by_mines, mines_remaining);
  }

  suffix[component_count].assign(mines_remaining + 1, 0.0L);
  suffix[component_count][0] = 1.0L;
  for (int i = component_count - 1; i >= 0; --i) {
    suffix[i] = ConvolveLimited(components[i].ways_by_mines, suffix[i + 1], mines_remaining);
  }

  const std::vector<long double> choose = BuildBinomialLimited(pool_cells, mines_remaining);

  const std::vector<long double> &all_component_ways = prefix[component_count];
  long double total_weight = 0.0L;
  long double pool_mine_weight = 0.0L;
  for (int mines_in_components = 0; mines_in_components <= mines_remaining; ++mines_in_components) {
    const int mines_in_pool = mines_remaining - mines_in_components;
    if (mines_in_pool < 0 || mines_in_pool > pool_cells || mines_in_pool >= static_cast<int>(choose.size())) {
      continue;
    }
    const long double ways =
        all_component_ways[mines_in_components] * choose[mines_in_pool];
    total_weight += ways;
    pool_mine_weight += ways * static_cast<long double>(mines_in_pool);
  }
  if (total_weight <= 0.0L) {
    return;
  }

  if (pool_cells > 0) {
    pool_risk = static_cast<double>(pool_mine_weight / (total_weight * static_cast<long double>(pool_cells)));
  }

  for (int i = 0; i < component_count; ++i) {
    const std::vector<long double> ways_without_current =
        ConvolveLimited(prefix[i], suffix[i + 1], mines_remaining);
    const std::vector<long double> rest_with_pool =
        ConvolveLimited(ways_without_current, choose, mines_remaining);

    long double denominator = 0.0L;
    const int local_cells = static_cast<int>(components[i].cells.size());
    std::vector<long double> numerators(local_cells, 0.0L);

    for (int mines_in_component = 0;
         mines_in_component <= mines_remaining &&
         mines_in_component < static_cast<int>(components[i].ways_by_mines.size());
         ++mines_in_component) {
      const int mines_elsewhere = mines_remaining - mines_in_component;
      if (mines_elsewhere < 0 || mines_elsewhere >= static_cast<int>(rest_with_pool.size())) {
        continue;
      }
      const long double rest_weight = rest_with_pool[mines_elsewhere];
      if (rest_weight == 0.0L) {
        continue;
      }
      denominator += components[i].ways_by_mines[mines_in_component] * rest_weight;
      for (int v = 0; v < local_cells; ++v) {
        numerators[v] += components[i].cell_mine_ways_by_mines[v][mines_in_component] * rest_weight;
      }
    }

    if (denominator <= 0.0L) {
      continue;
    }
    for (int v = 0; v < local_cells; ++v) {
      const int global_id = components[i].cells[v];
      mine_probability[global_id] = static_cast<double>(numerators[v] / denominator);
    }
  }
}

void EnumerateComponent(const std::vector<int> &component_cells, const std::vector<int> &component_constraints,
                        const std::vector<Constraint> &constraints, std::set<int> &forced_safe,
                        std::set<int> &forced_mines, std::vector<double> &mine_probability,
                        std::vector<EnumeratedComponentStats> &enumerated_components) {
  const int n = static_cast<int>(component_cells.size());
  if (n == 0 || n > 22) {
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
  std::vector<unsigned long long> ways_by_mines(n + 1, 0ULL);
  std::vector<std::vector<unsigned long long>> cell_mine_ways_by_mines(n, std::vector<unsigned long long>(n + 1, 0ULL));

  auto dfs = [&](auto &&self, int idx, int mines_used) -> void {
    if (idx == n) {
      for (int i = 0; i < m; ++i) {
        if (assigned_mines[i] != target[i]) {
          return;
        }
      }
      ++solution_count;
      ++ways_by_mines[mines_used];
      for (int v = 0; v < n; ++v) {
        mine_count[v] += static_cast<unsigned long long>(assigned[v]);
        if (assigned[v] == 1) {
          ++cell_mine_ways_by_mines[v][mines_used];
        }
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
        self(self, idx + 1, mines_used + val);
      }

      for (int con_idx : var_to_constraints[var]) {
        ++unassigned[con_idx];
        assigned_mines[con_idx] -= val;
      }
    }
  };

  dfs(dfs, 0, 0);

  if (solution_count == 0) {
    return;
  }

  EnumeratedComponentStats stats;
  stats.cells = component_cells;
  stats.ways_by_mines.resize(n + 1, 0.0L);
  stats.cell_mine_ways_by_mines.assign(n, std::vector<long double>(n + 1, 0.0L));
  for (int k = 0; k <= n; ++k) {
    stats.ways_by_mines[k] = static_cast<long double>(ways_by_mines[k]);
  }
  for (int v = 0; v < n; ++v) {
    for (int k = 0; k <= n; ++k) {
      stats.cell_mine_ways_by_mines[v][k] = static_cast<long double>(cell_mine_ways_by_mines[v][k]);
    }
  }
  enumerated_components.push_back(std::move(stats));

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
  int frontier_unknown_count = 0;
  for (int id = 0; id < total_cells; ++id) {
    if (!cell_to_constraints[id].empty()) {
      ++frontier_unknown_count;
    }
  }

  std::vector<double> mine_probability(total_cells, -1.0);
  std::vector<EnumeratedComponentStats> enumerated_components;
  int enumerated_cell_count = 0;
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

    const int size_before = static_cast<int>(enumerated_components.size());
    EnumerateComponent(component_cells, component_constraints, constraints, forced_safe, forced_mines, mine_probability,
                       enumerated_components);
    if (static_cast<int>(enumerated_components.size()) == size_before + 1) {
      enumerated_cell_count += static_cast<int>(component_cells.size());
    }
  }

  int mines_remaining = total_mines - flagged_count;
  mines_remaining = std::max(0, std::min(mines_remaining, unknown_count));
  double conditioned_pool_risk = -1.0;
  if (enumerated_cell_count == frontier_unknown_count) {
    const int pool_cells = std::max(0, unknown_count - frontier_unknown_count);
    ApplyGlobalMineConditioning(enumerated_components, mines_remaining, pool_cells, mine_probability,
                                conditioned_pool_risk);
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
    global_risk = static_cast<double>(mines_remaining) / static_cast<double>(unknown_count);
    if (conditioned_pool_risk >= 0.0) {
      global_risk = conditioned_pool_risk;
    }
  }

  int best_id = -1;
  double best_prob = std::numeric_limits<double>::infinity();
  int best_info = -1;
  constexpr double kProbTieEps = 1e-2;

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
      const bool better_prob = (p + kProbTieEps < best_prob);
      const bool same_prob = std::fabs(p - best_prob) <= kProbTieEps;
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
