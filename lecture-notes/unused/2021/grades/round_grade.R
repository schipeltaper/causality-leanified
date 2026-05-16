round_grade <- function(vec) {
  # apply FNWI grading scheme
  for( i in 1:length(vec) ) {
    if( !is.na(vec[i]) ) {
      if( vec[i] >= 9.75 ) {
        vec[i] = 10.0
      } else if( vec[i] >= 9.25 ) {
        vec[i] = 9.5
      } else if( vec[i] >= 8.75 ) {
        vec[i] = 9.0
      } else if( vec[i] >= 8.25 ) {
        vec[i] = 8.5
      } else if( vec[i] >= 7.75 ) {
        vec[i] = 8.0
      } else if( vec[i] >= 7.25 ) {
        vec[i] = 7.5
      } else if( vec[i] >= 6.75 ) {
        vec[i] = 7.0
      } else if( vec[i] >= 6.25 ) {
        vec[i] = 6.5
      } else if( vec[i] >= 5.5 ) {
        vec[i] = 6.0
      } else if( vec[i] >= 4.75 ) {
        vec[i] = 5.0
      } else if( vec[i] >= 4.25 ) {
        vec[i] = 4.5
      } else if( vec[i] >= 3.75 ) {
        vec[i] = 4.0
      } else if( vec[i] >= 3.25 ) {
        vec[i] = 3.5
      } else if( vec[i] >= 2.75 ) {
        vec[i] = 3.0
      } else if( vec[i] >= 2.25 ) {
        vec[i] = 2.5
      } else if( vec[i] >= 1.75 ) {
        vec[i] = 2.0
      } else if( vec[i] >= 1.25 ) {
        vec[i] = 1.5
      } else {
        vec[i] = 1.0
      }
    }
  }
  vec
}
