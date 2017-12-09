-- sql-indent used to think that the statement begins at the "FOR" keyword in
-- "V_SPORT_ZONE_FOR_SESSION"
create view V_SPORT_ZONE_FOR_SESSION as
  select S.id as session_id,
         VSZ.zone_id as zone_id,
         VSZ.zone_metric_id as zone_metric_id
    from A_SESSION S, V_SPORT_ZONE VSZ
   where S.sport_id = VSZ.sport_id
     and (((S.sub_sport_id is null or S.sub_sport_id = 0)
           and (VSZ.sub_sport_id is null or VSZ.sub_sport_id = 0))
          or S.sub_sport_id = VSZ.sub_sport_id)
     and S.start_time between VSZ.valid_from and VSZ.valid_until;
