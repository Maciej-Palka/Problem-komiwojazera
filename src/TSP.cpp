#include "TSP.hpp"

#include <algorithm>
#include <stack>
#include <optional>

std::ostream& operator<<(std::ostream& os, const CostMatrix& cm) {
    for (std::size_t r = 0; r < cm.size(); ++r) {
        for (std::size_t c = 0; c < cm.size(); ++c) {
            const auto& elem = cm[r][c];
            os << (is_inf(elem) ? "INF" : std::to_string(elem)) << " ";
        }
        os << "\n";
    }
    os << std::endl;

    return os;
}

/* PART 1 */

/**
 * Create path from unsorted path and last 2x2 cost matrix.
 * @return The vector of consecutive vertex.
 */
path_t StageState::get_path() {
    path_t path;
    if (unsorted_path_.size() == 0)
    {
        return path;
    }

    if (get_level() == matrix_.size() - 2)
    {
        vertex_t last1, last2;
        std::size_t k = 0;
        for (std::size_t r = 0; r < matrix_.size(); ++r)
        {
            for (std::size_t c = 0; c < matrix_.size(); ++c)
            {
                if (matrix_[r][c] != INF)
                {
                    if (k == 0)
                    {
                        last1 = vertex_t(r, c);
                        k++;
                    }
                    else if (k == 1)
                    {
                        last2 = vertex_t(r, c);
                        k++;
                    }
                }
            }
        }
        unsorted_path_.push_back(last1);
        unsorted_path_.push_back(last2);
    }
    std::size_t start_node = unsorted_path_[0].row;
    path.push_back(start_node);
    std::size_t current_node = unsorted_path_[0].col;

    while (path.size() < unsorted_path_.size())
    {
        path.push_back(current_node);
        auto it  = std::find_if(unsorted_path_.begin(), unsorted_path_.end(),
            [&current_node](const vertex_t& v)
            {
                return v.row == current_node;
            });

        if (it != unsorted_path_.end())
        {
            current_node = it->col;
        }
        else
        {
            current_node = start_node;
            break;
        }
    }
    return path;

}

/**
 * Get minimum values from each row and returns them.
 * @return Vector of minimum values in row.
 */
std::vector<cost_t> CostMatrix::get_min_values_in_rows() const {
    std::vector<cost_t> min_values;
    for (const auto& row : matrix_)
    {
        cost_t min_val = INF;
        for (cost_t val : row)
        {
            if (!is_inf(val) && val < min_val)
            {
                min_val = val;
            }
        }
        min_values.push_back((min_val == INF) ? 0 : min_val);
    }
    return min_values;
}

/**
 * Reduce rows so that in each row at least one zero value is present.
 * @return Sum of values reduced in rows.
 */
cost_t CostMatrix::reduce_rows() {
    std::vector<cost_t> min_values = get_min_values_in_rows();
    cost_t sum_reduced = 0;
    for (std::size_t r = 0; r <size(); ++r)
    {
        cost_t reduction = min_values [r];
        sum_reduced += reduction;
        for (std::size_t c =0; c <size(); ++c)
        {
            if (!is_inf(matrix_[r][c]))
            {
                matrix_[r][c] -= reduction;
            }
        }
        return sum_reduced;
    }
}

/**
 * Get minimum values from each column and returns them.
 * @return Vector of minimum values in columns.
 */
std::vector<cost_t> CostMatrix::get_min_values_in_cols() const {
    std::vector<cost_t> min_values(size(), INF);
    for (std::size_t c = 0; c< size(); ++c)
    {
        cost_t min_val = INF;
        for (std::size_t r = 0; r< size(); ++r)
        {
            if (!is_inf(matrix_[r][c]) && matrix_[r][c] < min_val)
            {
                min_val = matrix_[r][c];
            }
        }
        min_values[c] = (min_val == INF) ? 0 : min_val;
    }
    return min_values;
}

/**
 * Reduces rows so that in each column at least one zero value is present.
 * @return Sum of values reduced in columns.
 */
cost_t CostMatrix::reduce_cols() {
    std::vector<cost_t> min_values = get_min_values_in_cols();
    cost_t sum_reduced = 0;
    for (std::size_t c = 0; c <size(); ++c)
    {
        cost_t reduction = min_values[c];
        sum_reduced += reduction;
        for (std::size_t r =0; r < size(); ++r)
        {
            if (!is_inf(matrix_[r][c]))
            {
                matrix_[r][c] -= reduction;
            }
        }
    }
    return sum_reduced;
}

/**
 * Get the cost of not visiting the vertex_t (@see: get_new_vertex())
 * @param row
 * @param col
 * @return The sum of minimal values in row and col, excluding the intersection value.
 */
cost_t CostMatrix::get_vertex_cost(std::size_t row, std::size_t col) const {
    cost_t min_in_row = INF;
    for (std::size_t c = 0; c < size(); ++c)
    {
        if (c!=col && !is_inf(matrix_[row][c]) && matrix_[row][c] < min_in_row)
        {
            min_in_row = matrix_[row][c];
        }
    }

    cost_t min_in_col = INF;
    for (std::size_t r = 0; r < size(); ++r)
    {
        if (r!=row && !is_inf(matrix_[r][col]) && matrix_[r][col] < min_in_col)
        {
            min_in_col = matrix_[r][col];
        }
    }

    cost_t row_cost = (min_in_row == INF) ? 0 : min_in_row;
    cost_t col_cost = (min_in_col == INF) ? 0 : min_in_col;
    return row_cost + col_cost;
}

/* PART 2 */

/**
 * Choose next vertex to visit:
 * - Look for vertex_t (pair row and column) with value 0 in the current cost matrix.
 * - Get the vertex_t cost (calls get_vertex_cost()).
 * - Choose the vertex_t with maximum cost and returns it.
 * @param cm
 * @return The coordinates of the next vertex.
 */
NewVertex StageState::choose_new_vertex() {
    cost_t max_cost = -1;
    vertex_t best_vertex;

    for (std::size_t r =0; r < matrix_.size(); ++r)
    {
        for (std::size_t c = 0; c < matrix_.size(); ++c)
        {
            if (matrix_[r][c] == 0)
            {
                cost_t current_cost =matrix_.get_vertex_cost(r,c);
                if (current_cost > max_cost)
                {
                    max_cost = current_cost;
                    best_vertex = vertex_t(r,c);
                }
            }
        }
    }
    if (max_cost == -1)
    {
        return NewVertex(best_vertex, 0);
    }
    return NewVertex(best_vertex, max_cost);
}

/**
 * Update the cost matrix with the new vertex.
 * @param new_vertex
 */
void StageState::update_cost_matrix(vertex_t new_vertex) {
    std::size_t r = new_vertex.row;
    std::size_t c = new_vertex.col;

    for (std::size_t k = 0; k < matrix_.size(); ++k)
    {
        matrix_[r][k] = INF;
        matrix_[k][c] = INF;
    }
    matrix_[c][r] = INF;
}

/**
 * Reduce the cost matrix.
 * @return The sum of reduced values.
 */
cost_t StageState::reduce_cost_matrix() {
    cost_t cost = 0;
    cost += matrix_.reduce_rows();
    cost += matrix_.reduce_cols();
    return cost;
}

/**
 * Given the optimal path, return the optimal cost.
 * @param optimal_path
 * @param m
 * @return Cost of the path.
 */
cost_t get_optimal_cost(const path_t& optimal_path, const cost_matrix_t& m) {
    cost_t cost = 0;

    for (std::size_t idx = 1; idx < optimal_path.size(); ++idx) {
        cost += m[optimal_path[idx - 1]][optimal_path[idx]];
    }

    // Add the cost of returning from the last city to the initial one.
    cost += m[optimal_path[optimal_path.size() - 1]][optimal_path[0]];

    return cost;
}

/**
 * Create the right branch matrix with the chosen vertex forbidden and the new lower bound.
 * @param m
 * @param v
 * @param lb
 * @return New branch.
 */
StageState create_right_branch_matrix(cost_matrix_t m, vertex_t v, cost_t lb) {
    CostMatrix cm(m);
    cm[v.row][v.col] = INF;
    return StageState(cm, {}, lb);
}

/**
 * Retain only optimal ones (from all possible ones).
 * @param solutions
 * @return Vector of optimal solutions.
 */
tsp_solutions_t filter_solutions(tsp_solutions_t solutions) {
    cost_t optimal_cost = INF;
    for (const auto& s : solutions) {
        optimal_cost = (s.lower_bound < optimal_cost) ? s.lower_bound : optimal_cost;
    }

    tsp_solutions_t optimal_solutions;
    std::copy_if(solutions.begin(), solutions.end(),
                 std::back_inserter(optimal_solutions),
                 [&optimal_cost](const tsp_solution_t& s) { return s.lower_bound == optimal_cost; }
    );

    return optimal_solutions;
}

/**
 * Solve the TSP.
 * @param cm The cost matrix.
 * @return A list of optimal solutions.
 */
tsp_solutions_t solve_tsp(const cost_matrix_t& cm) {

    StageState left_branch(cm);

    // The branch & bound tree.
    std::stack<StageState> tree_lifo;

    // The number of levels determines the number of steps before obtaining
    // a 2x2 matrix.
    std::size_t n_levels = cm.size() - 2;

    tree_lifo.push(left_branch);   // Use the first cost matrix as the root.

    cost_t best_lb = INF;
    tsp_solutions_t solutions;

    while (!tree_lifo.empty()) {

        left_branch = tree_lifo.top();
        tree_lifo.pop();

        while (left_branch.get_level() != n_levels && left_branch.get_lower_bound() <= best_lb) {
            // Repeat until a 2x2 matrix is obtained or the lower bound is too high...

            if (left_branch.get_level() == 0) {
                left_branch.reset_lower_bound();
            }

            // 1. Reduce the matrix in rows and columns.
            cost_t new_cost = 0; // @TODO (KROK 1)

            // 2. Update the lower bound and check the break condition.
            left_branch.update_lower_bound(new_cost);
            if (left_branch.get_lower_bound() > best_lb) {
                break;
            }

            // 3. Get new vertex and the cost of not choosing it.
            NewVertex new_vertex = NewVertex(); // @TODO (KROK 2)

            // 4. @TODO Update the path - use append_to_path method.

            // 5. @TODO (KROK 3) Update the cost matrix of the left branch.

            // 6. Update the right branch and push it to the LIFO.
            cost_t new_lower_bound = left_branch.get_lower_bound() + new_vertex.cost;
            tree_lifo.push(create_right_branch_matrix(cm, new_vertex.coordinates,
                                                      new_lower_bound));
        }

        if (left_branch.get_lower_bound() <= best_lb) {
            // If the new solution is at least as good as the previous one,
            // save its lower bound and its path.
            best_lb = left_branch.get_lower_bound();
            path_t new_path = left_branch.get_path();
            solutions.push_back({get_optimal_cost(new_path, cm), new_path});
        }
    }

    return filter_solutions(solutions); // Filter solutions to find only optimal ones.
}
