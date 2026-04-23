
#[cfg(test)]
mod tests {
    use rkyv::{
      to_bytes,
      deserialize,
      rancor::Error,
      access_unchecked,
      Archive,
    };

    use astro_float_num::{
      BigFloat,
      //ArchivedBigFloat
    };

    #[test]
    fn to_from_rkyv() {
        let zero = &BigFloat::new(0);
        let bytes = to_bytes::<Error>(zero).unwrap();
        let archived =
          unsafe { access_unchecked::<<BigFloat as Archive>::Archived>(&bytes) };
        let bf : BigFloat = deserialize::<BigFloat, Error>(archived).unwrap();
        assert_eq!(bf,zero);
        
        let bf = BigFloat::from_f32(0.3, 64 + 1);
        let bytes = to_bytes::<Error>(&bf).unwrap();
        let archived =
          unsafe { access_unchecked::<<BigFloat as Archive>::Archived>(&bytes) };
        let bf2 : BigFloat = deserialize::<BigFloat, Error>(archived).unwrap();
        assert_eq!(bf,bf2);
    }
}
