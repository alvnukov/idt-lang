# Measured two-detector delay histogram

Source: Julian Münzberg, Franz Draxl, Saimon Filipe Covre da Silva, Yusuf Karli, Santanu Manna, Armando Rastelli, Gregor Weihs and Robert Keil, [dataset for *Fast and efficient demultiplexing of single photons from a GaAs quantum dot with resonantly enhanced electro-optic modulators*](https://doi.org/10.5281/zenodo.6337697), [paper](https://doi.org/10.1063/5.0091867). The authors released the data under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/). The source filename is retained. Only CRLF line endings were normalized to LF for Git; no bins, counts, or headers were changed.

| File | Bytes | SHA-256 |
| --- | ---: | --- |
| [Deposited CSV](https://zenodo.org/records/6337697/files/HBT_QD5_resonant_no_AB_att_0.0043_software_delay_16-44-38.csv?download=1) | 68,128 | `e0767eeac5644e955c35962384943e6dd4e3cfcc1347ff1c0644fd2dca463556` |
| [Repository CSV](HBT_QD5_resonant_no_AB_att_0.0043_software_delay_16-44-38.csv) | 63,127 | `91b17e8c360b61dbdf7ede4f60bc3bdd3b283b43174ebda51037a4c45ac905b4` |

The 5,000 rows are delay-bin counts from a cross-correlation measurement, with units in the header. They are **not** per-pump records: neither triggers with no detection nor the ordered pair of detections underlying any count is identifiable. No fabricated trial sequence or additional specimen is included. The fixed-pump-period comparison uses the source histogram, not digitized plot heights or the output of a randomness extractor.
