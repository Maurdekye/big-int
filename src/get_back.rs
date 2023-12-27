/// Safely retrieve items from a collection with negative indexing.
pub trait GetBack {
  type Item;

  /// Safely retrieve items from a collection with negative indexing.
  /// Returns `None` if the index is larger than the length of the collection.
  fn get_back(&self, index: usize) -> Option<Self::Item>;
}

impl<T: Copy> GetBack for Vec<T> {
  type Item = T;
  fn get_back(&self, index: usize) -> Option<Self::Item> {
      self.len()
          .checked_sub(index)
          .and_then(|index| self.get(index)).copied()
  }
}

/// Safely retrieve a mutable reference from a collection with negative indexing.
pub trait GetBackMut {
  type Item;

  /// Safely retrieve a mutable reference from a collection with negative indexing.
  /// Returns `None` if the index is larger than the length of the collection.
  fn get_back_mut(&mut self, index: usize) -> Option<&mut Self::Item>;
}

impl<T> GetBackMut for Vec<T> {
  type Item = T;
  fn get_back_mut(&mut self, index: usize) -> Option<&mut Self::Item> {
      self.len()
          .checked_sub(index)
          .and_then(|index| self.get_mut(index))
  }
}