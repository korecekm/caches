
pub(crate) trait Cache<K, V> {
    fn try_get(&mut self, key: &K) -> Option<&V>;
    fn insert(&mut self, key: K, value: V);
}
