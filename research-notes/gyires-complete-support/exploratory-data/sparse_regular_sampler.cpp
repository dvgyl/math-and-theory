#include <algorithm>
#include <charconv>
#include <cmath>
#include <iomanip>
#include <iostream>
#include <numeric>
#include <random>
#include <stdexcept>
#include <string_view>
#include <vector>

using Matrix = std::vector<std::vector<int>>;

int integer_argument(const char* text) {
  std::string_view value(text);
  int result = 0;
  const auto parsed = std::from_chars(value.data(), value.data() + value.size(), result);
  if (parsed.ec != std::errc{} || parsed.ptr != value.data() + value.size())
    throw std::invalid_argument("Arguments must be integers.");
  return result;
}

long double permanent(const Matrix& matrix) {
  const int n = static_cast<int>(matrix.size());
  const std::size_t count = std::size_t{1} << n;
  std::vector<long double> values(count, 0);
  values[0] = 1;
  for (std::size_t subset = 1; subset < count; ++subset) {
    const int row = __builtin_popcountll(subset) - 1;
    for (std::size_t remaining = subset; remaining; remaining &= remaining - 1) {
      const int column = __builtin_ctzll(remaining);
      values[subset] += matrix[row][column] * values[subset ^ (std::size_t{1} << column)];
    }
  }
  return values.back();
}

int main(int argc, char** argv) {
  try {
    if (argc > 4) throw std::invalid_argument("Use: sampler [order [degree [samples]]].");
    const int n = argc > 1 ? integer_argument(argv[1]) : 12;
    const int degree = argc > 2 ? integer_argument(argv[2]) : 3;
    const int samples = argc > 3 ? integer_argument(argv[3]) : 10;
    if (n < 1 || n > 22 || degree < 1 || degree > n || samples < 1)
      throw std::invalid_argument("Require 1 <= order <= 22, 1 <= degree <= order, and samples >= 1.");
    std::mt19937 generator(199);
    long double constant = 1;
    for (int k = 1; k <= n; ++k) constant *= static_cast<long double>(k) / n;
    bool below_one = false;
    for (int sample = 0; sample < samples; ++sample) {
      Matrix matrix(n, std::vector<int>(n, 0));
      std::vector<int> permutation(n);
      std::iota(permutation.begin(), permutation.end(), 0);
      for (int d = 0; d < degree; ++d) {
        bool disjoint = false;
        for (int attempt = 0; attempt < 1000000 && !disjoint; ++attempt) {
          std::shuffle(permutation.begin(), permutation.end(), generator);
          disjoint = true;
          for (int i = 0; i < n; ++i)
            if (matrix[i][permutation[i]]) disjoint = false;
        }
        if (!disjoint) throw std::runtime_error("Sampling limit reached. The requested sample set is incomplete.");
        for (int i = 0; i < n; ++i) matrix[i][permutation[i]] = 1;
      }
      Matrix gram(n, std::vector<int>(n, 0));
      for (int i = 0; i < n; ++i)
        for (int j = 0; j < n; ++j)
          for (int k = 0; k < n; ++k) gram[i][j] += matrix[i][k] * matrix[j][k];
      const long double value = permanent(matrix);
      const long double gram_value = permanent(gram);
      const long double ratio = value * value / (constant * gram_value);
      if (!std::isfinite(ratio) || value <= 0 || gram_value <= 0)
        throw std::runtime_error("The numerical permanent calculation failed.");
      std::cout << std::setprecision(17) << n << ' ' << degree << ' ' << sample
                << " per=" << value << " gram=" << gram_value << " ratio=" << ratio << '\n';
      if (ratio < 1) {
        below_one = true;
        for (const auto& row : matrix) {
          for (int entry : row) std::cout << entry << ' ';
          std::cout << '\n';
        }
      }
      std::cout.flush();
      if (!std::cout) throw std::runtime_error("Cannot write the sample output.");
    }
    std::cerr << "Completed " << samples << " numerical samples.\n";
    if (below_one) std::cerr << "A numerical ratio is below one. Exact verification is required.\n";
    return below_one ? 1 : 0;
  } catch (const std::exception& error) {
    std::cerr << error.what() << '\n';
    return 2;
  }
}
