pub(crate) trait Cache<K, V> {
    fn try_get(&mut self, key: &K) -> Option<&V>;
    /// Expects that key isn't already present!
    fn insert(&mut self, key: K, value: V);
}
