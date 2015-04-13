#include <vector>
#include <array>
#include <string>
#include <iostream>
#include <algorithm>
#include <iterator>
#include <exception>
#include <sstream>
#include <bitset>
#include <ctime>
#include <thread>
#include <mutex>
#include <functional>
#include <cassert>

#define likely(x)   __builtin_expect((x),1)
#define unlikely(x) __builtin_expect((x),0)

typedef std::array<int, 3> Point;
typedef std::vector<Point> Points;

typedef std::array<int, 9> Matrix;

typedef unsigned long Code;
typedef std::vector<Code>  CodeVec;

typedef std::vector<int> IdxVec;

std::string print_code(const Code& code, const int size)
{
   std::ostringstream ost;
   if (size == 4)
   {
      ost << (std::bitset<64>(code));
   }
   else
   if (size == 2)
   {
      ost << (std::bitset<8>(code));
   }
   else
   {
      throw std::runtime_error("print code: size");
   }
   return ost.str();
}

bool operator< (const Point& a, const Point& b)
{
   return a[0] != b[0] ? a[0] < b[0]
        : a[1] != b[1] ? a[1] < b[1]
        :                a[2] < b[2];
}

int count_points(const Code& code)
{
   int cnt = 0;
   Code c  = code;    

   while (c)
   {
      if (c & 0x1)
      {
         ++cnt;
      }
      c = c >> 1; 
   }

   return cnt;
}

std::string print_points(const Points& points)
{
   std::ostringstream ost;
   for (const auto& p : points)
   {
      ost << "(" << p[0] << "," << p[1] << "," << p[2] << "),";
   }
   return ost.str();
}

Point P_sum(const Point& a, const Point& b)
{
   return { a[0]+b[0], a[1]+b[1], a[2]+b[2] };
}

inline const int& M_at(const Matrix& m, int i, int j)
{
   return m[3 * i + j];
}

inline int& M_at(Matrix& m, int i, int j)
{
   return m[3 * i + j];
}

Matrix M_mul(const Matrix& a, const Matrix& b)
{
   Matrix m;
   for (int i=0; i < 3; ++i)
   for (int j=0; j < 3; ++j)
   {
      int v = 0;
      for (int k = 0; k < 3; ++k)
      {
         v += M_at(a, i,k) * M_at(b, k,j);
      }
      M_at(m, i,j) = v;
   }
   return m;
}

Point M_mul(const Matrix& m, const Point& x)
{
   Point y;
   for (int i=0; i < 3; ++i)
   {
      int v = 0;
      for (int j=0; j < 3; ++j)
      {
         v += M_at(m, i,j) * x[j];
      }
      y[i] = v;
   }
   return y;
}

Points M_mul(const Matrix& m, const Points& points)
{
   Points ret;
   for (const auto& p : points)
   {
      ret.push_back(M_mul(m, p));
   }
   return ret;
}

Points P_sum(const Point& p0, const Points& points)
{
   Points ret;
   for (const auto& p : points)
   {
      ret.push_back(P_sum(p0, p));
   }
   return ret;
} 

Points P_mul(const int n, const Points& points)
{
   Points ret;
   for (const auto& p : points)
   {
      ret.push_back({p[0] * n, p[1] * n, p[2] * n});
   }
   return ret;
}

Points P_div(const int n, const Points& points)
{
   Points ret;
   for (const auto& p : points)
   {
      if (n == 0 || p[0] % n || p[1] % n || p[2] % n)
      {
         throw std::runtime_error("P_div");
      }
      ret.push_back({p[0] / n, p[1] / n, p[2] / n});
   }
   return ret;
}

class InCubeChecker
{
   const int size;

public:
   InCubeChecker(const int size_)
      : size(size_)
   {}

   bool do_check(const Point& p) const
   {
      return (0 <= p[0] && p[0] < size &&
              0 <= p[1] && p[1] < size &&
              0 <= p[2] && p[2] < size);
   }
};

template<typename Checker>
bool check_points(const Points& points, const Checker& checker)
{
   for (const auto& p : points)
   {
      if (! checker.do_check(p))
      {
         return false;
      }
   }
   return true;
}

struct Element
{
   std::string name;
   Points points;

   Element(const std::string& name_, const Points& points_)
      : name(name_), points(points_)
   {
      normalize();
   }
 
   Element(const Element& o)
      : name(o.name), points(o.points)
   {
      normalize();
   }

   Element& operator= (const Element& o)
   {
      name   = o.name;
      points = o.points;
      normalize();
   }

private:
   void normalize()
   {
      std::sort(points.begin(), points.end());
   }
};
typedef std::vector<Element>    ElementVec;
typedef std::vector<ElementVec> ElementVecVec;

struct Rotator
{
   std::string name;
   Matrix matrix;

   Rotator()
      : name("0"), matrix()
   {}
   Rotator(const std::string& name_, const Matrix& matrix_)
      : name(name_), matrix(matrix_)
   {}
   bool operator== (const Rotator& o) const
   {
      return matrix == o.matrix;
   }
   bool operator<  (const Rotator& o) const
   {
      return matrix < o.matrix;
   }
};
typedef std::vector<Rotator> RotatorVec;

ElementVec init_elements_4x4()
{
   return ElementVec ({
      Element("e0", {{0,1,0},{1,0,0},{1,1,0},{1,2,0},{2,1,0}}),
      Element("e1", {{0,0,0},{1,0,0},{1,1,0},{1,2,0},{2,1,0}}),
      Element("e2", {{0,0,0},{0,1,0},{1,1,0},{1,2,0},{2,2,0}}),
      Element("e3", {{0,0,0},{0,1,0},{0,2,0},{0,0,1},{1,0,0}}),
      Element("e4", {{0,0,0},{0,1,0},{0,2,0},{0,1,1},{1,0,0}}),
      Element("e5", {{0,0,0},{0,1,0},{0,2,0},{0,1,1},{1,1,0}}),
      Element("e6", {{0,0,0},{0,0,1},{1,0,0},{1,1,0},{1,2,0}}),
      Element("e7", {{0,0,0},{0,1,0},{0,2,0},{0,2,1},{1,0,0}}),
      Element("e8", {{0,0,0},{0,1,0},{0,2,0},{1,1,0},{1,1,1}}),
      Element("e9", {{0,1,0},{0,2,0},{1,0,0},{1,0,1},{1,1,0}}),
      Element("eA", {{0,1,0},{0,2,0},{0,1,1},{1,0,0},{1,1,0}}),
      Element("eB", {{0,1,0},{0,1,1},{0,2,1},{1,0,0},{1,1,0}}),
      Element("eC", {{0,0,0},{0,1,0},{1,0,0},{1,0,1}}),
   });
}

ElementVec init_elements_2x2()
{
   return ElementVec ({
      Element("e0", {{0,0,0},{1,0,0},{0,1,0},{1,1,0},{0,0,1},{1,0,1}}),
      Element("e1", {{0,0,0},{0,0,1}})
   });
}

Rotator combine(const Rotator& a, const Rotator& b)
{
   return Rotator(a.name + b.name,
                  M_mul(a.matrix, b.matrix));
}

RotatorVec init_rotators()
{
   const Rotator I_rotator(
              "___I", { 1, 0, 0,
                        0, 1, 0,
                        0, 0, 1 }
   );

   const RotatorVec Z_rotators({
      Rotator("+z90", { 0, 1, 0,
                       -1, 0, 0,
                        0, 0, 1 }),

      Rotator("-z90", { 0,-1, 0,
                        1, 0, 0,
                        0, 0, 1 }),

      Rotator("|zSM", {-1, 0, 0,
                        0,-1, 0,
                        0, 0, 1 })
   });

   const RotatorVec Y_rotators({
      Rotator("+y90", { 0, 0, 1,
                        0, 1, 0,
                       -1, 0, 0 }),

      Rotator("-y90", { 0, 0,-1,
                        0, 1, 0,
                        1, 0, 0 }),

      Rotator("|ySM", {-1, 0, 0,
                        0, 1, 0,
                        0, 0,-1 })
   });

   const RotatorVec X_rotators({
      Rotator("+x90", { 1, 0, 0,
                        0, 0,-1,
                        0, 1, 0 }),

      Rotator("-x90", { 1, 0, 0,
                        0, 0, 1,
                        0,-1, 0 }),

      Rotator("|xSM", { 1, 0, 0,
                        0,-1, 0,
                        0, 0,-1 })
   });

   RotatorVec rotators;

   rotators.push_back(I_rotator);
   
   for (const auto& zr : Z_rotators)
   {
      rotators.push_back(zr);
   }
   for (const auto& yr : Y_rotators)
   {
      rotators.push_back(yr);
   }
   for (const auto& xr : X_rotators)
   {
      rotators.push_back(xr);
   }
   for (const auto& zr : Z_rotators)
   for (const auto& yr : Y_rotators)
   {
      rotators.push_back(combine(zr,yr));
   }
   for (const auto& zr : Z_rotators)
   for (const auto& xr : X_rotators)
   {
      rotators.push_back(combine(zr,xr));
   }
   for (const auto& yr : Y_rotators)
   for (const auto& xr : X_rotators)
   {
      rotators.push_back(combine(yr,xr));
   }

   std::sort(rotators.begin(), rotators.end());
   const auto& it = std::unique  (rotators.begin(), rotators.end());
   rotators.resize (std::distance(rotators.begin(), it));

   std::cout << "Generated rotators: " << rotators.size() << std::endl;

   return rotators;
}

ElementVec generate_rotations(const Element& element,
                              const RotatorVec& rotators)
{
   ElementVec rotations;

   for (const auto& r : rotators)
   {   
      rotations.push_back(Element(element.name + r.name,
                                  M_mul(r.matrix, element.points)));
   }

   return rotations;
}

ElementVec generate_instances(const Element& element, const int size)
{
   ElementVec instances;

   for (int x = 0; x < size; ++x)
   for (int y = 0; y < size; ++y)
   for (int z = 0; z < size; ++z)
   {
      const Point  shift  = { x, y, z };
      const Points points = P_sum(shift, element.points);

      if (check_points(points, InCubeChecker(size)))
      {
         std::ostringstream ost;
         ost << x << "," << y << "," << z << "-" << element.name;
         instances.push_back(Element(ost.str(), points));
      }
   }

   return instances;
}

ElementVec generate_instances(const ElementVec& elements, const int size)
{
   ElementVec instances;

   for (const auto& e : elements)
   {
      const ElementVec i = generate_instances(e, size);
      instances.insert(instances.end(), i.begin(), i.end());
   }

   return instances;
}

template<typename Checker>
ElementVec remove_equivalent(const ElementVec& elements,
                             const Checker& checker)
{
   ElementVec instances;

   for (int i=0, ii=elements.size(); i < ii; ++i)
   {
      const Element& e = elements[i];
      bool duplicate_found = false;

      for (int j=0, jj=instances.size(); j < jj; ++j)
      {
         if (checker.equal(e, instances[j]))
         {
            duplicate_found = true;
            break;
         }
      }

      if (! duplicate_found)
      {
         instances.push_back(e);
      }
   }

   return instances;
}

ElementVec remove_duplicates(const ElementVec& elements)
{
   struct Checker
   {
      bool equal(const Element& a, const Element& b) const
      {
         return (a.points == b.points);
      }
   };

   return remove_equivalent(elements, Checker());
}

ElementVec remove_congruent(const ElementVec& elements,
                            const RotatorVec& rotators,
                            const int size)
{
   struct Checker
   {
      const RotatorVec& rotators;
      const int size;
      const Point shift_p2;
      const Point shift_m2;

      Checker(const RotatorVec& rotators_, const int size_)
         : rotators(rotators_)
         , size(size_)
         , shift_p2({+(size-1),+(size-1),+(size-1)})
         , shift_m2({-(size-1),-(size-1),-(size-1)})
      {}

      bool equal(const Element& a, const Element& b) const
      {
         bool found_congruent = false;
         Points points;

         for (const auto& r : rotators)
         {
            points = a.points;
            points = P_mul(2,        points);
            points = P_sum(shift_m2, points);
            points = M_mul(r.matrix, points);
            points = P_sum(shift_p2, points);
            points = P_div(2,        points);

            if (! check_points(points, InCubeChecker(size)))
            {
               std::cout << print_points(points) << std::endl;
               throw std::runtime_error("remove_congruent: not in_cube");
            }

            Element e ("", points); // for normalization
            if (e.points == b.points)
            {
               found_congruent = true;
               break;
            }
         }

         return found_congruent;
      }
   };

   return remove_equivalent(elements, Checker(rotators, size));
}

Code encode(const Element& element, const int size)
{
   Code code = 0;

   InCubeChecker in_cube(size);

   for (const auto& p : element.points)
   {
      if (! in_cube.do_check(p))
      {
         throw std::runtime_error("encode: not in cube");
      }

      int shift = size * size * p[0] + size * p[1] + p[2];
      code |= (Code(1) << shift);
   }

   return code;
}

std::vector<CodeVec> encode(const ElementVecVec& element_instances,
                            const int size)
{
   std::vector<CodeVec> element_codes;

   for (const auto& ei : element_instances)
   {
      CodeVec codes;
      for (const auto& e : ei)
      {
         codes.push_back(encode(e, size));
      }
      element_codes.push_back(codes);
   }
   
   return element_codes;
}

class IterationReporter
{
   std::mutex&  m_log_mutex;

   const int    m_thread_id;
   const time_t m_start_time;
   time_t       m_last_time;
   long         m_last_iteration;

public:
   IterationReporter(const int thread_id, std::mutex& log_mutex)
      : m_thread_id      (thread_id)
      , m_log_mutex      (log_mutex)
      , m_start_time     (time(0))
      , m_last_time      (time(0))
      , m_last_iteration (0)
   {}

   void report(const long iteration, const IdxVec& i, const IdxVec& ii)
   {
      const time_t current_time   = time(0);
      const int    total_duration = current_time - m_start_time + 1;
      const long   total_ops      = double(iteration) / 1000000;
      const double avg_ops        = double(total_ops) / total_duration;
      const int    last_duration  = current_time - m_last_time + 1;
      const double last_ops       = double(iteration - m_last_iteration)
                                           / 1000000 / last_duration;

      m_last_time      = current_time;
      m_last_iteration = iteration;

      std::lock_guard<std::mutex> guard (m_log_mutex);

      std::cout << "Thread "       << m_thread_id
                << ": Done "       << total_ops      << " M ops"
                << ", Time "       << total_duration << " sec"
                << ", Ops (avg) "  << avg_ops        << " M/sec"
                << ", Last "       << last_duration  << " sec"
                << ", Ops (last) " << last_ops       << " M/sec"
                << std::endl;

      for (int n=0, nn=i.size(); n < nn; ++n)
      {
         std::cout << i[n] << ":" << ii[n] << "|";
      }
      std::cout << std::endl;
   }
};

class SolutionReporter
{
   std::mutex& m_log_mutex;

   const ElementVecVec& m_element_instances;

public:
   SolutionReporter(std::mutex& log_mutex,
                    const ElementVecVec& element_instances)
      : m_log_mutex         (log_mutex)
      , m_element_instances (element_instances)
   {}

   void report(const IdxVec& i)
   {
      std::lock_guard<std::mutex> guard(m_log_mutex);

      std::cout << "========== SOLUTION ==========" << std::endl;
      for (int n=0, nn=i.size(); n < nn; ++n)
      {
         const Element& e = m_element_instances[n][i[n]];
         std::cout << e.name << ": " << print_points(e.points)  << std::endl;
      }
      std::cout << "==============================" << std::endl;
   }
};

void thread_worker(const int thread_id,  std::mutex& log_mutex,
                   const int ARENA_SIZE, const Code ARENA_FULL,
                   ElementVecVec element_instances)
{
   const std::vector<CodeVec> element_codes = 
                       encode(element_instances, ARENA_SIZE);

   CodeVec arena;
   IdxVec  i;
   IdxVec  ii;

   for (const auto& c : element_codes)
   {
      arena.push_back(0);
      i.push_back(0);
      ii.push_back(c.size());
   }

   int e  = 0;
   int ee = element_codes.size();

   long iteration = 0;

   IterationReporter iteration_reporter(thread_id, log_mutex);
   SolutionReporter  solution_reporter (log_mutex, element_instances);

   while (e > 0 || i[0] < ii[0])
   {
      ++iteration;

      if (unlikely(iteration % (long(10000)*1000000) == 0))
      {
         iteration_reporter.report(iteration, i, ii);
      }

      const Code code = element_codes[e][i[e]];

      if (e == 0)
      {
         arena[0] = code;
         goto next_e;
      }

      if (arena[e-1] & code)
      {
         goto next_i;
      }

      arena[e] = arena[e-1] | code;

      if (unlikely(arena[e] == ARENA_FULL))
      {
         solution_reporter.report(i);
         goto next_i;
      }

      next_e:

      if (e + 1 < ee)
      {
         ++e;
         continue;
      }

      next_i:

      while (e > 0 && i[e] + 1 == ii[e])
      {
         i[e] = 0;
         --e;
      }

      ++i[e];
   }
}

int main()
{
   const int MAX_THREAD  = 2;
#if 1
   const int  ARENA_SIZE = 4;
   const Code ARENA_FULL = 0xFFFFFFFFFFFFFFFF;
   const ElementVec elements = init_elements_4x4();
#else
   const int  ARENA_SIZE = 2;
   const Code ARENA_FULL = 0xFF;
   const ElementVec elements = init_elements_2x2();
#endif

   const RotatorVec rotators = init_rotators();

   ElementVecVec element_instances;
   for (const auto& e : elements)
   {
      const ElementVec rotations = generate_rotations(e, rotators);
      const ElementVec instances = generate_instances(rotations, ARENA_SIZE);
      const ElementVec unique    = remove_duplicates(instances);
      element_instances.push_back(unique);
   }

   if (element_instances.empty())
   {
      throw std::runtime_error("element_instances empty");
   }

   element_instances[0] = remove_congruent(element_instances[0], 
                                           rotators, ARENA_SIZE);

   std::cout << "Generated instances: |"; 
   for (const auto& ei : element_instances)
   {
      std::cout << ei.size() << "|";
   }
   std::cout << std::endl;

   std::mutex log_mutex;
   std::vector<std::thread> threads;

   for (int thread_id=0; thread_id < MAX_THREAD; ++thread_id)
   {
      ElementVecVec instances;
      for (int n=0, nn=element_instances.size(); n < nn-1; ++n)
      {
         instances.push_back(element_instances[n]);
      }

      ElementVec this_thread_instances;
      const ElementVec& last_element_instances = element_instances.back();
      for (int n=0, nn=last_element_instances.size(); n < nn; ++n)
      {
         if (n % MAX_THREAD == thread_id)
         {
            this_thread_instances.push_back(last_element_instances[n]);
         }
      }

      instances.push_back(this_thread_instances);

      threads.push_back(std::thread (thread_worker,
                                     thread_id, std::ref(log_mutex), 
                                     ARENA_SIZE, ARENA_FULL, instances));
   }

   for (auto& thread : threads)
   {
      thread.join();
   }
}

