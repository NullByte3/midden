//! Number, size, date and duration formatting for the report.

use std::time::Duration;

pub fn fmt_duration(duration: Duration) -> String {
    let secs = duration.as_secs_f64();
    if secs < 1.0 {
        format!("{}ms", duration.as_millis())
    } else if secs < 60.0 {
        format!("{secs:.1}s")
    } else {
        let total = secs.round() as u64;
        let (minutes, seconds) = (total / 60, total % 60);
        if minutes < 60 {
            format!("{minutes}m{seconds:02}s")
        } else {
            format!("{}h{:02}m{:02}s", minutes / 60, minutes % 60, seconds)
        }
    }
}

pub(crate) fn human_bytes(bytes: f64) -> String {
    let (mut value, mut unit) = (bytes, "B");
    for next in ["KB", "MB", "GB", "TB"] {
        if value < 1024.0 {
            break;
        }
        (value, unit) = (value / 1024.0, next);
    }
    if unit == "B" { format!("{value:.0}B") } else { format!("{value:.1}{unit}") }
}

pub(crate) fn commas(n: u64) -> String {
    let digits = n.to_string();
    let mut out = String::with_capacity(digits.len() + digits.len() / 3);
    for (i, digit) in digits.chars().enumerate() {
        if i > 0 && (digits.len() - i).is_multiple_of(3) {
            out.push(',');
        }
        out.push(digit);
    }
    out
}

/// Unix millis to `2026-07-31 19:29 UTC` via civil-from-days, to avoid a date crate.
pub(crate) fn date_utc(ms: i64) -> String {
    let secs = ms.div_euclid(1000);
    let (days, day_secs) = (secs.div_euclid(86_400), secs.rem_euclid(86_400));
    let from_march = days + 719_468;
    let (era, day_of_era) = (from_march.div_euclid(146_097), from_march.rem_euclid(146_097));
    let year_of_era = (day_of_era - day_of_era / 1460 + day_of_era / 36_524 - day_of_era / 146_096) / 365;
    let day_of_year = day_of_era - (365 * year_of_era + year_of_era / 4 - year_of_era / 100);
    let march_month = (5 * day_of_year + 2) / 153;
    let day = day_of_year - (153 * march_month + 2) / 5 + 1;
    let month = if march_month < 10 { march_month + 3 } else { march_month - 9 };
    let year = year_of_era + era * 400 + i64::from(month <= 2);
    format!("{year:04}-{month:02}-{day:02} {:02}:{:02} UTC", day_secs / 3600, day_secs % 3600 / 60)
}
