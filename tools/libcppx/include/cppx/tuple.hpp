// -*- C++ -*-

#ifndef CPPX_TUPLE_HPP
#define CPPX_TUPLE_HPP

#include <cstddef>
#include <tuple>

namespace cppx
{
namespace meta
{
inline namespace v1
{

// -------------------------------------------------------------------------- //
// Reflected tuples

// Presents a tuple-like interface for reflection queries. 
template<typename Ops>
struct reflected_tuple
{
  static constexpr std::size_t size() { 
    return Ops::size(); 
  }
  static constexpr bool empty() {
    return size() == 0;
  }
};

// Returns the Ith element of the reflected tuple.
template<std::size_t I, typename Ops>
constexpr auto 
get(reflected_tuple<Ops> const&) -> decltype(Ops::template get<I>()) {
  return Ops::template get<I>();
}

// Returns the Ith element of the reflected tuple as a constant expression.
template<std::size_t I, typename Ops>
constexpr auto 
cget(reflected_tuple<Ops> const&) -> decltype(Ops::template get<I>()) {
  return Ops::template get<I>();
}

// -------------------------------------------------------------------------- //
// Tuple algorithms

// For each

namespace detail
{

// TODO: Add support for non-const tuples?
//
// Base case.
template<std::size_t I,typename T, typename F>
constexpr std::enable_if_t<I == T::size(), void>
tuple_for_each_recursive(T const&, F) { 
}

// Recursive step.
template<std::size_t I, typename T, typename F>
constexpr std::enable_if_t<I < T::size(), void>
tuple_for_each_recursive(T const& t, F f) {
  f(cget<I>(t));
  tuple_for_each_recursive<I + 1>(t, f);
}

} // namespace detail


// Driver, for ease of use.
template<typename T, typename F>
constexpr void
tuple_for_each(T const& t, F f) {
  detail::tuple_for_each_recursive<0>(t, f);
}


// Count if

namespace detail
{
template<template<typename> typename P>
struct count_type_if_fn 
{
  int& n;

  // Matching case.
  template<typename T>
  constexpr std::enable_if_t<P<T>::value> operator()(T const& t) { 
    ++n; 
  }
  
  // Non-matching case.
  template<typename T>
  constexpr std::enable_if_t<!P<T>::value> operator()(T const& t) { }
};
} // namespace detail


// Returns the number of elements in t whose types satisfy a unary type trait.
template<template<typename> typename P, typename T>
constexpr int 
tuple_count_type_if(T const& t) {
  int n = 0;
  detail::count_type_if_fn<P> f{n};
  tuple_for_each(t, f);
  return n;
}


// -------------------------------------------------------------------------- //
// Tuple algorithms

// A filter applied to a tuple.
template<typename Ops, template<typename> typename Pred>
struct filtered_tuple
{
  static constexpr std::size_t size() { 
    return tuple_count_type_if<Pred>(reflected_tuple<Ops>()); 
  }
  static constexpr bool empty() {
    return size() == 0;
  }
};


namespace detail
{

// The type of nth element of a tuple.
//
// TODO: This should be equivalent to tuple_element. I don't think I need it.
template<int N, typename T>
using constant_element_type_t = decltype(cget<N>(std::declval<T>()));


// A helper class for accessing the filtered element of a tuple. The first
// parameter determines whether the nested type is defined.
template<bool B, int N, typename T>
struct safe_element_type
{
  using type = constant_element_type_t<N, T>;
};

// FIXME: If the predicate is a type trait, this might fail in bad ways.
template<int N, typename T>
struct safe_element_type<false, N, T>
{
  using type = void; 
};

template<int N, typename T>
using safe_element_type_t = typename safe_element_type<N < T::size(), N, T>::type;


template<std::size_t N, template<typename> typename P, typename T>
constexpr bool is_satisfied() 
{
  return P<safe_element_type_t<N, T>>::value;
}

// A helper class used to implement get<>() and cget<> for filtered tuples.
struct filtered_get
{
  // Off the end. This returns void, which is almost certainly unusable at
  // the point of use.
  template<std::size_t I, std::size_t J, template<typename> typename P, typename T>
  static constexpr auto get(
      T const& t, 
      std::enable_if_t<I == T::size()>* = 0)
  {
    return;
  }

  // I < N, J == 0 and cget<I>(t) satisfies P. Returns cget<I>(t).
  template<std::size_t I, std::size_t J, template<typename> typename P, typename T>
  static constexpr auto get(
      T const& t, 
      std::enable_if_t<
          I < T::size() && J == 0 && is_satisfied<I, P, T>()
      >* = 0)
  {
    return cget<I>(t);
  }

  // I < N, J == 0 and cget<I>(t) does not satisfy P. Recurse.
  template<std::size_t I, std::size_t J, template<typename> typename P, typename T>
  static constexpr auto get(
      T const& t, 
      std::enable_if_t<
          I < T::size() && J == 0 && !is_satisfied<I, P, T>()
      >* = 0)
  {
    return get<I + 1, 0, P>(t);
  }

  // I < N, J > 0 and cget<I>(t) satisfies P. Recurse, decrementing J.
  template<std::size_t I, std::size_t J, template<typename> typename P, typename T>
  static constexpr auto get(
      T const& t,
      std::enable_if_t<
            I < T::size() && 0 < J && is_satisfied<I, P, T>()
      >* = 0)
  {
    return get<I + 1, J - 1, P>(t);
  }

  // I < N, J > 0 and cget<I>(t) does not satisfies P. Recurse.
  template<std::size_t I, std::size_t J, template<typename> typename P, typename T>
  static constexpr auto get(
      T const& t,
      std::enable_if_t<
          I < T::size() && 0 < J && !is_satisfied<I, P, T>()
      >* = 0)
  {
    return get<I + 1, J, P>(t);
  }
};

} // namespace detail

// Returns the Ith element in the filtered tuple.
template<std::size_t I, typename Ops, template<typename> typename Pred>
constexpr auto 
get(filtered_tuple<Ops, Pred> const& t)
{
  return detail::filtered_get::get<0, I, Pred>(reflected_tuple<Ops>());
}

// Returns the Ith element in the filtered tuple as a constant expression.
template<std::size_t I, typename Ops, template<typename> typename Pred>
constexpr auto 
cget(filtered_tuple<Ops, Pred> const&)
{
  return detail::filtered_get::get<0, I, Pred>(reflected_tuple<Ops>());
}

} // inline namespace v1
} // namespace meta
} // namespace cppx

// Import all of the meta facilities into the standard library.
//
// TODO: this exists because I haven't rewritten the lookup code in the
// compiler to find declarations in a non-standard namespace. This works
// just as well.
namespace std
{

template<typename Ops>
struct tuple_size<cppx::meta::reflected_tuple<Ops>>
  : std::integral_constant<std::size_t, Ops::size()>
{ };

template<std::size_t I, typename Ops>
struct tuple_element<I, cppx::meta::reflected_tuple<Ops>>
{
  using type = decltype(Ops::template get<I>());
};

template<typename Ops, template<typename> typename Pred>
struct tuple_size<cppx::meta::filtered_tuple<Ops, Pred>>
  : std::integral_constant<std::size_t, cppx::meta::filtered_tuple<Ops, Pred>::size()>
{ };

template<std::size_t I, typename Ops, template<typename> typename Pred>
struct tuple_element<I, cppx::meta::filtered_tuple<Ops, Pred>>
{
  using type = decltype(get<I>(std::declval<cppx::meta::filtered_tuple<Ops, Pred>>()));
};

} // namespace std

#endif // CPPX_TUPLE_HPP

